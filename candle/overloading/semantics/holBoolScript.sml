(*
  Define semantics for the Boolean operations and show the definitions are
  correct.
*)
open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory
     holSemanticsTheory holSemanticsExtraTheory setSpecTheory

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory"holBool"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

Overload p[local] = ``Var (strlit "p") Bool``
Overload FAp[local] = ``Forall (strlit "p") Bool``
Overload q[local] = ``Var (strlit "q") Bool``
Overload FAq[local] = ``Forall (strlit "q") Bool``
Overload r[local] = ``Var (strlit "r") Bool``
Overload FAr[local] = ``Forall (strlit "r") Bool``
Overload f[local] = ``Var (strlit "f") (Fun Bool (Fun Bool Bool))``
Overload A[local] = ``Tyvar (strlit "A")``
Overload P[local] = ``Var (strlit "P") (Fun A Bool)``
Overload x[local] = ``Var (strlit "x") A``
Overload FAx[local] = ``Forall (strlit "x") A``

val sigs = [is_true_sig_def, is_false_sig_def, is_implies_sig_def, is_and_sig_def,
            is_or_sig_def, is_not_sig_def, is_forall_sig_def, is_exists_sig_def]

(* TODO: move *)
Theorem ext_type_frag_builtins_simps:
  (!δ. ext_type_frag_builtins δ Bool = boolset) /\
  (!δ dom rng.
       ext_type_frag_builtins δ (Fun dom rng) =
       Funspace (ext_type_frag_builtins δ dom) (ext_type_frag_builtins δ rng))
Proof
  rw[] >> simp[Once ext_type_frag_builtins_def]
QED

val Boolrel_def = xDefine"Boolrel"`
  Boolrel0 ^mem R =
      (Abstract boolset (Funspace boolset boolset)
           (λp. (Abstract boolset boolset
              (λq. Boolean (R (p = True) (q = True))))))`
Overload Boolrel = ``Boolrel0 ^mem``

val is_true_interpretation_def = xDefine"is_true_interpretation"`
  is_true_interpretation0 ^mem γ ⇔ γ(strlit "T",Bool) = True:'U`
Overload is_true_interpretation = ``is_true_interpretation0 ^mem``

val is_and_interpretation_def = xDefine"is_and_interpretation"`
  is_and_interpretation0 ^mem γ ⇔ γ(strlit "/\\", Fun Bool (Fun Bool Bool)) = Boolrel $/\`
Overload is_and_interpretation = ``is_and_interpretation0 ^mem``

val is_implies_interpretation_def = xDefine"is_implies_interpretation"`
  is_implies_interpretation0 ^mem γ ⇔ γ(strlit "==>",Fun Bool (Fun Bool Bool)) = Boolrel $==>`
Overload is_implies_interpretation = ``is_implies_interpretation0 ^mem``

val is_forall_interpretation_def = xDefine"is_forall_interpretation"`
  is_forall_interpretation0 ^mem γ δ ty ⇔
    γ(strlit "!",Fun (Fun ty Bool) Bool) = Abstract (Funspace (δ ty) boolset) boolset
              (λP. Boolean (∀x. x <: δ ty ⇒ Holds P x))`
Overload is_forall_interpretation = ``is_forall_interpretation0 ^mem``

val is_exists_interpretation_def = xDefine"is_exists_interpretation"`
  is_exists_interpretation0 ^mem γ δ ty ⇔
    γ(strlit "?",Fun (Fun ty Bool) Bool) =
       Abstract (Funspace (δ ty) boolset) boolset
              (λP. Boolean (∃x. x <: (δ ty) ∧ Holds P x))`
Overload is_exists_interpretation = ``is_exists_interpretation0 ^mem``

val is_or_interpretation_def = xDefine"is_or_interpretation"`
  is_or_interpretation0 ^mem γ ⇔ γ(strlit "\\/",Fun Bool (Fun Bool Bool)) = Boolrel $\/`
Overload is_or_interpretation = ``is_or_interpretation0 ^mem``

val is_false_interpretation_def = xDefine"is_false_interpretation"`
  is_false_interpretation0 ^mem γ ⇔ γ(strlit "F",Bool) = False:'U`
Overload is_false_interpretation = ``is_false_interpretation0 ^mem``

val is_not_interpretation_def = xDefine"is_not_interpretation"`
  is_not_interpretation0 ^mem γ ⇔ γ(strlit "~",Fun Bool Bool) = Abstract boolset boolset (λp. Boolean (p ≠ True))`
Overload is_not_interpretation = ``is_not_interpretation0 ^mem``

val ints = [is_true_interpretation_def,is_and_interpretation_def,is_implies_interpretation_def,
            is_forall_interpretation_def,is_exists_interpretation_def,is_or_interpretation_def,
            is_false_interpretation_def,is_not_interpretation_def]

val is_bool_interpretation_def = xDefine"is_bool_interpretation"`
  is_bool_interpretation0 ^mem sig δ γ ⇔
    is_std_interpretation (types_of_frag(total_fragment sig)) δ γ ∧
    is_true_interpretation γ ∧
    is_and_interpretation γ ∧
    is_implies_interpretation γ ∧
    (!ty. ty ∈ ground_types sig ==> is_forall_interpretation γ δ ty) ∧
    (!ty. ty ∈ ground_types sig ==> is_exists_interpretation γ δ ty) ∧
    is_or_interpretation γ ∧
    is_false_interpretation γ ∧
    is_not_interpretation γ`
Overload is_bool_interpretation = ``is_bool_interpretation0 ^mem``

val is_bool_interpretation_ext_def = xDefine"is_bool_interpretation_ext"`
  is_bool_interpretation_ext0 ^mem sig δ γ ⇔
  is_bool_interpretation sig
    (ext_type_frag_builtins δ)
    (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)`
Overload is_bool_interpretation_ext = ``is_bool_interpretation_ext0 ^mem``

Theorem boolrel_in_funspace:
  is_set_theory ^mem ⇒ Boolrel R <: Funspace boolset (Funspace boolset boolset)
Proof
  rw[Boolrel_def] >> match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset]
QED

val _ = export_rewrites["boolrel_in_funspace"]

val Defs = [TrueDef_def, AndDef_def, ImpliesDef_def, ForallDef_def, ExistsDef_def, OrDef_def, FalseDef_def, NotDef_def]

Theorem bool_term_ok_rator:
   is_bool_sig sig ==>
   (term_ok sig (Const (strlit "/\\") (Fun Bool (Fun Bool Bool))) /\
    term_ok sig (Const (strlit "\\/") (Fun Bool (Fun Bool Bool))) /\
    term_ok sig (Const (strlit "~") (Fun Bool Bool)) /\
    term_ok sig (Const (strlit "==>") (Fun Bool (Fun Bool Bool))) /\
    term_ok sig (Const (strlit "!") (Fun (Fun A Bool) Bool)) /\
    term_ok sig (Const (strlit "?") (Fun (Fun A Bool) Bool)))
Proof
  rw[is_bool_sig_def,is_std_sig_def,is_and_sig_def,is_or_sig_def,is_not_sig_def,
     is_implies_sig_def,is_forall_sig_def,is_exists_sig_def,term_ok_def,type_ok_def]
QED

fun init_tac q1 q2 ty rule =
    rw[Once ext_term_frag_builtins_def] >> fs[models_def] >>
    first_x_assum(qspec_then `^q1 === ^q2` mp_tac) >>
    impl_tac >- (unabbrev_all_tac >> imp_res_tac extends_sub >> fs[SUBSET_DEF] >>
                 TRY(first_x_assum match_mp_tac) >> EVAL_TAC) >>
    `term_ok sig ^q2` by (
      simp([bool_term_ok,term_ok_equation,term_ok_clauses] @ Defs)) >>
    fs[satisfies_t_def,satisfies_def] >> rw[] >>
    first_x_assum(qspec_then `K ^ty` mp_tac) >>
    impl_tac >-
      (fs[tyvars_def,type_ok_def,ground_terms_uninst_def,ground_types_def] >>
       qexists_tac `Bool` >>
       imp_res_tac term_ok_welltyped >>
       simp[EQUATION_HAS_TYPE_BOOL,welltyped_equation,
            typeof_equation,ground_types_def,tyvars_def,type_ok_def] >>
        EVAL_TAC) >>
    qspec_then `sig` assume_tac total_fragment_is_fragment >>
    drule rule >> rpt(disch_then drule) >>
    strip_tac >> disch_then(qspec_then `v` mp_tac) >>
    impl_tac >-
      (simp[valuates_frag_builtins] >>
       match_mp_tac terms_of_frag_uninst_term_ok >> fs[ground_types_def] >>
       simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator] >>
       imp_res_tac term_ok_welltyped >> fs(Defs @ [typeof_equation])) >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    rpt(disch_then drule) >>
    qmatch_goalsub_abbrev_tac `a1 === a2` >>
    disch_then(qspecl_then [`a1`,`a2`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`a1`,`a2`] >>
    impl_tac >-
      (conj_tac
       >- (match_mp_tac terms_of_frag_uninst_term_ok >> fs[ground_types_def] >>
           simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator]) >>
       simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator] >>
       imp_res_tac term_ok_welltyped >> fs(Defs@[typeof_equation]) >>
       match_mp_tac terms_of_frag_uninst_term_ok >>
       simp[type_ok_def,tyvars_def] >> fs[ground_types_def]) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true] >>
    simp[termsem_def] >> simp[Once ext_term_frag_builtins_def] >>
    disch_then kall_tac

(* TODO: parameterise previous tac further? *)
fun init_tac2 q1 q2 ty rule =
    rw[Once ext_term_frag_builtins_def] >> fs[models_def] >>
    first_x_assum(qspec_then `^q1 === ^q2` mp_tac) >>
    impl_tac >- (fs[SUBSET_DEF] >>
                 first_x_assum match_mp_tac >>
                 EVAL_TAC) >>
    `term_ok (tyenv,tmenv) ^q2` by (
      simp([bool_term_ok,term_ok_equation,term_ok_clauses] @ Defs)) >>
    fs[satisfies_t_def,satisfies_def] >> rw[] >>
    first_x_assum(qspec_then `K ^ty ` mp_tac) >>
    impl_tac >-
      (fs[tyvars_def,type_ok_def,ground_terms_uninst_def,ground_types_def] >>
       qexists_tac `Bool` >>
       imp_res_tac term_ok_welltyped >>
       simp[EQUATION_HAS_TYPE_BOOL,welltyped_equation,
            typeof_equation,ground_types_def,tyvars_def,type_ok_def] >>
        EVAL_TAC) >>
    qspec_then `(tyenv,tmenv)` assume_tac total_fragment_is_fragment >>
    drule rule >> rpt(disch_then drule) >>
    strip_tac >> disch_then(qspec_then `v` mp_tac) >>
    impl_tac >-
      (simp[valuates_frag_builtins] >>
       match_mp_tac terms_of_frag_uninst_term_ok >> fs[ground_types_def] >>
       simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator] >>
       imp_res_tac term_ok_welltyped >> fs(Defs @ [typeof_equation])) >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    rpt(disch_then drule) >>
    qmatch_goalsub_abbrev_tac `a1 === a2` >>
    disch_then(qspecl_then [`a1`,`a2`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`a1`,`a2`] >>
    impl_tac >-
      (conj_tac
       >- (match_mp_tac terms_of_frag_uninst_term_ok >> fs[ground_types_def] >>
           simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator]) >>
       simp[type_ok_def,tyvars_def,term_ok_equation,bool_term_ok,bool_term_ok_rator] >>
       imp_res_tac term_ok_welltyped >> fs(Defs@[typeof_equation]) >>
       match_mp_tac terms_of_frag_uninst_term_ok >>
       simp[type_ok_def,tyvars_def] >> fs[ground_types_def]) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_true] >>
    simp[termsem_def] >> simp[Once ext_term_frag_builtins_def] >>
    disch_then kall_tac

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

Theorem boolean_eq_boolean:
  is_set_theory ^mem ==> !a b. Boolean a = Boolean b <=> a = b
Proof
  rw[boolean_def] >> rw[true_neq_false]
QED

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

Theorem apply_boolrel_rw:
  is_set_theory ^mem ⇒
    ∀b1 b2 b3. b1 <: boolset ∧ b2 <: boolset ⇒
      Boolrel R ' b1 ' b2 = Boolean (R (b1 = True) (b2 = True))
Proof
  metis_tac[apply_boolrel]
QED

(* TODO: move *)
val builtins_std_assignment = Q.prove(
  `is_std_type_assignment(ext_type_frag_builtins δ)`,
  rw[is_std_type_assignment_def]
  >> CONV_TAC(RATOR_CONV(PURE_ONCE_REWRITE_CONV [ext_type_frag_builtins_def]))
  >> rw[]);

(* TODO: move *)
Theorem is_std_interpretation_total_fragment:
 !sig δ γ.
   is_std_interpretation
     (types_of_frag (total_fragment sig))
     (ext_type_frag_builtins δ)
     (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
Proof
  rw[is_std_interpretation_def,builtins_std_assignment,total_fragment_def,types_of_frag_def,builtin_closure_idem]
  >> TRY(rename1 `Fun _ _ ∈ _` >>
         fs[IN_DEF] >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [builtin_closure_cases]) >>
         rw[nonbuiltin_types_def,is_builtin_type_def])
  >> CONV_TAC(RATOR_CONV(PURE_ONCE_REWRITE_CONV [ext_term_frag_builtins_def]))
  >> rw[]
QED

Theorem bool_has_bool_interpretation:
  is_set_theory ^mem ⇒
    ∀ctxt δ γ. theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
             models δ γ (thyof (mk_bool_ctxt ctxt)) ⇒
             is_bool_interpretation_ext (sigof(mk_bool_ctxt ctxt)) δ γ
Proof
  rw[] >>
  simp[is_bool_interpretation_ext_def,is_bool_interpretation_def,is_std_interpretation_total_fragment] >>
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
    init_tac ``Const (strlit "T") Bool`` ``TrueDef`` ``Bool`` exists_valuation_bool >>
    fs[TrueDef_def] >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    rpt(disch_then drule) >>
    disch_then(qspecl_then [`Abs p p`,`Abs p p`] mp_tac) >>
    impl_tac >-
      (simp[] >>
       match_mp_tac terms_of_frag_uninst_term_ok >>
       simp[type_ok_def,tyvars_def,term_ok_def]) >>
    simp[boolean_eq_true]) >>
  conj_asm1_tac >- (
    init_tac ``Const (strlit "/\\") (Fun Bool (Fun Bool Bool))`` ``AndDef`` ``Bool`` exists_valuation_bool >>
    fs[AndDef_def] >>
    simp[termsem_def] >>
    imp_res_tac term_ok_welltyped >>
    fs[] >> simp[typeof_equation] >>
    PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[] >>
    PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[Boolrel_def] >>
    drule abstract_eq >> disch_then match_mp_tac >>
    ntac 2 strip_tac >> simp[] >>
    rpt conj_asm2_tac
    >- simp[]
    >- (match_mp_tac (MP_CANON abstract_in_funspace) >> rw[boolean_in_boolset]) >>
    drule abstract_eq >> disch_then match_mp_tac >>
    ntac 2 strip_tac >> simp[] >>
    rpt conj_asm2_tac
    >- simp[]
    >- simp[boolean_in_boolset] >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ a1 a2 (a3 === a4)` >>
    disch_then(qspecl_then [`a2`,`a1`,`a3`,`a4`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
    impl_tac
    >- (conj_tac >-
         (fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >>
          simp[Once ext_type_frag_builtins_def]) >>
        fs[term_ok_equation,term_ok_clauses,bool_term_ok] >>
        conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >>
        fs[term_ok_clauses,type_ok_def,tyvars_def,bool_term_ok]) >>
    simp[] >> disch_then kall_tac >>
    simp[termsem_def,combinTheory.UPDATE_def] >>
    simp[ext_type_frag_builtins_def] >>
    rw[boolean_def] >>
    qmatch_assum_abbrev_tac`f1 = f2` >>
    rename1 `_ ' b1 ' b2` >>
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
        simp[] >> match_mp_tac (UNDISCH abstract_in_funspace) >> simp[boolean_in_boolset]) >>
      fs[Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_def,mem_boolset] >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_def,mem_boolset]) >>
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
    metis_tac[]) >>
  conj_asm1_tac >- (
    init_tac ``Const (strlit "==>") (Fun Bool (Fun Bool Bool))`` ``ImpliesDef`` ``Bool`` exists_valuation_bool >>
    fs[ImpliesDef_def] >>
    simp[termsem_def] >>
    imp_res_tac term_ok_welltyped >>
    fs[] >> simp[typeof_equation] >>
    PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[] >>
    PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[Boolrel_def] >>
    drule abstract_eq >> disch_then match_mp_tac >>
    ntac 2 strip_tac >> simp[] >>
    rpt conj_asm2_tac
    >- simp[]
    >- (match_mp_tac (MP_CANON abstract_in_funspace) >> rw[boolean_in_boolset]) >>
    drule abstract_eq >> disch_then match_mp_tac >>
    ntac 2 strip_tac >> simp[] >>
    rpt conj_asm2_tac
    >- simp[]
    >- simp[boolean_in_boolset] >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ a1 a2 (a3 === a4)` >>
    disch_then(qspecl_then [`a2`,`a1`,`a3`,`a4`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
    impl_tac
    >- (conj_tac >-
         (fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >>
          simp[Once ext_type_frag_builtins_def]) >>
        fs[term_ok_equation,term_ok_clauses,bool_term_ok] >>
        conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >>
        fs[term_ok_clauses,type_ok_def,tyvars_def,bool_term_ok]) >>
    simp[] >> disch_then kall_tac >>
    simp[termsem_def,combinTheory.UPDATE_def] >>
    simp[ext_type_frag_builtins_def] >>
    rw[boolean_def] >>
    qmatch_assum_abbrev_tac`f1 = f2` >>
    rename1 `_ ' b1 ' b2` >>
    `Boolrel $/\ ' b1 = Abstract boolset boolset (λb2. Boolean (b1 = True ∧ b2 = True))` by (
      unabbrev_all_tac >> simp[Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >> simp[boolean_in_boolset]) >>
    `Boolrel $/\ ' b1 ' b2 =  Boolean (b1 = True ∧ b2 = True)` by (
      rveq >> unabbrev_all_tac >> simp[] >>
      match_mp_tac apply_abstract_matchable >> simp[boolean_in_boolset]) >>
    unabbrev_all_tac >> fs[boolean_def] >> every_case_tac >> fs[] >>
    rfs[mem_boolset] >> fs[]) >>
  conj_asm1_tac >- (
    init_tac ``Const (strlit "!") (Fun (Fun A Bool) Bool)`` ``ForallDef`` ``ty:type`` exists_valuation >>
    fs[ForallDef_def,termsem_def] >> simp[Once ext_type_frag_builtins_def] >>
    imp_res_tac term_ok_welltyped >> fs[] >>
    simp[typeof_equation] >>
    qpat_abbrev_tac `a1 = ext_type_frag_builtins δ ty` >>
    PURE_ONCE_REWRITE_TAC [ext_type_frag_builtins_def] >> simp[] >>
    drule abstract_eq >> disch_then match_mp_tac >>
    simp[boolean_in_boolset] >>
    ntac 2 strip_tac >>
    conj_asm2_tac >- simp[boolean_in_boolset] >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ av sigma` >>
    disch_then(qspecl_then [`sigma`,`av`,`P`,`Abs x True`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`sigma`,`av`] >>
    impl_tac >- (
      conj_tac >- (
        fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >> simp[Once ext_type_frag_builtins_def] >>
        CONV_TAC(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))) >>
        simp[]) >>
      fs[term_ok_clauses,bool_term_ok] >>
      conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[type_ok_def,ground_types_def,term_ok_clauses,bool_term_ok]
    ) >>
    simp[] >> disch_then kall_tac >>
    simp[termsem_def,combinTheory.UPDATE_def] >>
    simp[Once ext_type_frag_builtins_def] >>
    simp[holds_def] >>
    rw[boolean_def] >- (
      simp[true_neq_false] >> pop_assum mp_tac >> simp[] >>
      rw[] >> match_mp_tac apply_abstract_matchable >>
      simp[mem_boolset]
      ) >>
   simp[true_neq_false] >> qpat_x_assum `_ <> _` mp_tac >> simp[] >>
   drule in_funspace_abstract >> disch_then drule >>
   strip_tac >> rveq >>
   drule abstract_eq >> disch_then match_mp_tac >>
   rw[mem_boolset] >> metis_tac[apply_abstract]) >>
  conj_asm1_tac >- (
    init_tac ``Const (strlit "?") (Fun (Fun A Bool) Bool)`` ``ExistsDef`` ``ty:type`` exists_valuation >>
    fs[ExistsDef_def,termsem_def] >> simp[Once ext_type_frag_builtins_def] >>
    imp_res_tac term_ok_welltyped >> fs[] >>
    simp[typeof_equation] >>
    qpat_abbrev_tac `a1 = ext_type_frag_builtins δ ty` >>
    PURE_ONCE_REWRITE_TAC [ext_type_frag_builtins_def] >> simp[] >>
    simp[combinTheory.UPDATE_def] >>
    `Bool ∈ ground_types sig` by(simp[ground_types_def,tyvars_def,type_ok_def]) >>
    first_x_assum drule >> simp[] >> disch_then kall_tac >>
    drule abstract_eq >> disch_then match_mp_tac >>
    simp[boolean_in_boolset] >>
    ntac 2 strip_tac >>
    conj_asm2_tac >- simp[boolean_in_boolset] >>
    simp[ext_type_frag_builtins_def] >>
    qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand = _` >>
    drule apply_abstract >>
    disch_then(qspecl_then [`rator`,`rand`,`Funspace boolset boolset`,`boolset`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
    impl_tac >- (
      simp[boolean_in_boolset] >> match_mp_tac (MP_CANON abstract_in_funspace) >>
      rw[] >> match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      asm_exists_tac >> simp[] >>
      match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
      match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      qexists_tac `Funspace a1 boolset` >> simp[] >>
      conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace) >>
      simp[]
      >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `boolset` >>
          rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
          metis_tac[]) >>
      simp[] >> metis_tac[boolean_in_boolset]
      ) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_boolean] >>
    `inhabited a1`
      by(unabbrev_all_tac >> match_mp_tac(MP_CANON inhabited_ext) >>
         simp[] >> qexists_tac `FST(total_fragment(sigof (mk_bool_ctxt ctxt)))` >>
         fs[total_fragment_def,is_frag_interpretation_def,
            is_sig_fragment_def,is_type_frag_interpretation_def,ground_types_builtin_closure]) >>
    rename1 `e ⋲ a1` >> rename1 `ff ⋲ Funspace _ boolset` >>
    `ff ' e ⋲ boolset` by(metis_tac[apply_in_rng]) >>
    reverse EQ_TAC >- (
      rw[holds_def] >>
      drule apply_abstract >>
      qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
      disch_then(qspecl_then [`rator`,`rand`,`boolset`,`boolset`] mp_tac) >>
      MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
      impl_tac >- (
        simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
        asm_exists_tac >> simp[] >> match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
        match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
        qexists_tac `Funspace a1 boolset` >>
        conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace)
        >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
            simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            qexists_tac `boolset` >>
            rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
            metis_tac[]) >>
        simp[] >> metis_tac[boolean_in_boolset]) >>
      simp[] >> disch_then kall_tac >>
      qmatch_goalsub_abbrev_tac `_ ' b1 ' b2 = b3` >>
      drule(GEN_ALL apply_boolrel) >>
      disch_then(qspecl_then [`$==>`,`b1`,`b2`,`b3`] mp_tac) >>
      MAP_EVERY qunabbrev_tac [`b1`,`b2`,`b3`] >>
      impl_tac >- (
        conj_tac >- (
          match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `Funspace a1 boolset` >>
          conj_tac >> match_mp_tac (MP_CANON abstract_in_funspace)
          >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              qexists_tac `boolset` >> simp[mem_boolset] >>
              match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
              match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              metis_tac[]) >>
          simp[] >> metis_tac[boolean_in_boolset]) >>
        simp[boolean_eq_true] >>
        qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
        drule apply_abstract >>
        disch_then(qspecl_then [`rator`,`rand`,`Funspace a1 boolset`,`boolset`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
        impl_tac >- (
          simp[boolean_in_boolset] >> match_mp_tac(MP_CANON abstract_in_funspace) >>
          rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
          metis_tac[apply_in_rng]) >>
        simp[boolean_eq_true] >> disch_then kall_tac >>
        disch_then drule >>
        drule apply_abstract >>
        qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
        disch_then(qspecl_then [`rator`,`rand`,`a1`,`boolset`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
        impl_tac >- (
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          asm_exists_tac >> simp[] >> match_mp_tac(MP_CANON apply_in_rng) >>
          simp[] >> qexists_tac `boolset` >> simp[boolrel_in_funspace,mem_boolset]) >>
        simp[] >> disch_then kall_tac >>
        qmatch_goalsub_abbrev_tac `_ ' b1 ' b2 = b3` >>
        drule(GEN_ALL apply_boolrel) >>
        disch_then(qspecl_then [`$==>`,`b1`,`b2`,`x''`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`b1`,`b2`,`b3`] >>
        impl_tac >- (rfs[mem_boolset,boolean_def,true_neq_false]) >>
        simp[]) >>
      simp[])
    >- (
      simp[holds_def] >>
      qmatch_goalsub_abbrev_tac`Abstract boolset boolset rator` >>
      drule apply_abstract >>
      disch_then(qspec_then `rator` mp_tac) >>
      disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
      disch_then(qspecl_then [`boolset`,`boolset`] mp_tac) >>
      `!x. x ⋲ boolset ==> rator x ⋲ boolset` by
       (qunabbrev_tac `rator` >> rw[] >> match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> asm_exists_tac >> simp[] >>
        match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `boolset` >>
        simp[boolrel_in_funspace] >>
        match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `Funspace a1 boolset` >>
        conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace)
        >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
            simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            qexists_tac `boolset` >>
            rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
            metis_tac[]) >>
        simp[] >> metis_tac[boolean_in_boolset]) >>
      simp[] >> disch_then kall_tac >>
      qunabbrev_tac `rator` >> fs[] >>
      qho_match_abbrev_tac `(∀x. x ⋲ boolset ⇒ Boolrel R ' (Abstract d1 bs i1 ' (Abstract d2 bs (i2 x))) ' x = True) ==> _` >>
      `∀x. x <: boolset ⇒ Abstract d1 bs i1 ' (Abstract d2 bs (i2 x)) = i1 (Abstract d2 bs (i2 x))` by (
        rw[] >>
        match_mp_tac apply_abstract_matchable >>
        simp[Abbr`bs`,Abbr`d1`,Abbr`i1`,boolean_in_boolset] >>
        match_mp_tac (UNDISCH abstract_in_funspace) >>
        rw[Abbr`i2`] >>
        apply_abstract_tac ) >>
      simp[Abbr`R`,Abbr`bs`,Abbr`d2`] >>
      `∀x. (λm. i2 x m) = (i2 x)` by metis_tac[ETA_AX] >>
      `∀x a. x <: boolset /\ a <: a1 ⇒ Abstract a1 boolset (i2 x) ' a = i2 x a` by (
        rw[] >>
        match_mp_tac apply_abstract_matchable >>
        rw[Abbr`i2`] >>
        apply_abstract_tac ) >>
      simp[Abbr`i1`] >>
      simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true] >>
      simp[Abbr`i2`] >>
      `!x. x ⋲ a1 ==> ff ' x ⋲ boolset` by metis_tac[apply_in_rng] >>
      simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true] >>
      qunabbrev_tac `d1` >>
      ntac 7 (pop_assum kall_tac) >>
      metis_tac[mem_boolset,true_neq_false])) >>
  conj_asm1_tac >-
    (init_tac ``Const (strlit "\\/") (Fun Bool (Fun Bool Bool))`` ``OrDef`` ``Bool`` exists_valuation_bool >>
     fs[OrDef_def] >> simp[termsem_def,combinTheory.UPDATE_def] >>
     PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[] >>
     PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[] >>
     simp[SimpR ``$=``,Boolrel_def] >>
     match_mp_tac (MP_CANON abstract_eq) >>
     simp[] >> ntac 2 strip_tac >>
     conj_asm2_tac >- fs[] >>
     conj_asm1_tac >- (match_mp_tac(MP_CANON abstract_in_funspace) >> metis_tac[boolean_in_boolset]) >>
     match_mp_tac (MP_CANON abstract_eq) >> simp[] >>
     ntac 2 strip_tac >>
     `Bool ∈ ground_types sig` by(simp[ground_types_def,tyvars_def,type_ok_def]) >>
     last_x_assum drule >> simp[] >> disch_then kall_tac >>
     conj_asm2_tac >- fs[] >>
     conj_asm1_tac >- metis_tac[abstract_in_funspace,boolean_in_boolset] >>
     PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[] >>
     qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' rand` >>
     drule apply_abstract >>
     disch_then(qspecl_then [`rator`,`rand`,`dom`,`rng`] mp_tac) >>
     MAP_EVERY qunabbrev_tac [`rator`,`rand`,`dom`,`rng`] >>
     impl_tac >- (simp[boolean_in_boolset] >> apply_abstract_tac) >>
     simp[] >> disch_then kall_tac >> simp[boolean_eq_boolean] >>
     simp[holds_def] >>
     qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' _` >>
     drule apply_abstract >>
     disch_then(qspecl_then [`rator`] mp_tac) >>
     disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
     disch_then(qspecl_then [`rng`,`dom`] mp_tac) >>
     `∀x. x ⋲ dom ==> rator x ⋲ rng` by
       (unabbrev_all_tac >> rw[] >> match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `boolset` >>
        conj_tac >> match_mp_tac(MP_CANON apply_in_rng)
        >- (simp[] >> asm_exists_tac >> simp[] >>
            match_mp_tac(MP_CANON apply_in_rng) >>
            simp[] >> qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
            match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            asm_exists_tac >> simp[] >>
            match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            asm_exists_tac >> simp[]) >>
        simp[] >> metis_tac[boolrel_in_funspace,apply_in_rng]) >>
     MAP_EVERY qunabbrev_tac [`dom`,`rng`] >>
     simp[] >> disch_then kall_tac >>
     qunabbrev_tac `rator` >>
     simp[apply_boolrel_rw,boolean_in_boolset] >>
     simp[boolean_eq_true] >> metis_tac[mem_boolset]) >>
  conj_asm1_tac >- (
    init_tac ``Const (strlit "F") Bool`` ``FalseDef`` ``Bool`` exists_valuation_bool >>
    fs[FalseDef_def] >>
    simp[termsem_def] >>
    `Bool ∈ ground_types sig` by(simp[ground_types_def,tyvars_def,type_ok_def]) >>
    last_x_assum drule >> simp[] >> disch_then kall_tac >>
    PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[combinTheory.UPDATE_def] >>
    qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' rand` >>
    drule apply_abstract >>
    disch_then(qspecl_then [`rator`,`rand`,`dom`,`rng`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`rator`,`rand`,`dom`,`rng`] >>
    impl_tac >- (simp[boolean_in_boolset] >> apply_abstract_tac) >>
    simp[] >> disch_then kall_tac >>
    rw[boolean_def,true_neq_false] >>
    pop_assum(qspec_then `False` mp_tac) >>
    simp[mem_boolset,holds_def,apply_abstract,true_neq_false])
  >- (
    init_tac ``Const (strlit "~") (Fun Bool Bool)`` ``NotDef`` ``Bool`` exists_valuation_bool >>
    simp[NotDef_def,termsem_def,combinTheory.UPDATE_def] >>
    PURE_ONCE_REWRITE_TAC [ext_type_frag_builtins_def] >> simp[] >>
    match_mp_tac(MP_CANON abstract_eq) >>
    simp[] >> ntac 2 strip_tac >>
    conj_asm2_tac >- simp[] >>
    simp[boolean_in_boolset] >>
    simp[apply_boolrel_rw,mem_boolset,boolean_eq_boolean,true_neq_false])
QED

Theorem bool_ops_not_overloadable_mk_bool_ctxt:
  bool_ops_not_overloadable (mk_bool_ctxt ctxt) <=> bool_ops_not_overloadable ctxt
Proof
  fs[bool_ops_not_overloadable_def,overloadable_in_def,mk_bool_ctxt_def]
QED

Theorem overloadable_in_APPEND:
  overloadable_in name (ctxt ++ ctxt')
  = (overloadable_in name ctxt ∨ overloadable_in name ctxt')
Proof
  rw[overloadable_in_def,EQ_IMP_THM,GSYM EXISTS_OR_THM]
  >> TRY (goal_assum (first_x_assum o mp_then Any mp_tac))
  >> qmatch_asmsub_abbrev_tac `NewConst name ty`
  >> qexists_tac `ty` >> asm_rewrite_tac[]
QED

Theorem ConstDef_extends_not_overloadable:
  (ConstDef name def)::ctxt extends []
  ⇒ ~overloadable_in name ctxt
Proof
  rw[extends_NIL_CONS_extends,updates_cases,overloadable_in_def,constspec_ok_def,is_builtin_name_def]
  >> rw[MEM_SPLIT]
  >> CCONTR_TAC
  >> fs[] >> fs[]
QED

Theorem ConstDef_extends_not_overloadable':
  ctxt' ++ (ConstDef name def)::ctxt extends []
  ⇒ ~overloadable_in name (ctxt' ++ (ConstDef name def)::ctxt)
Proof
  reverse (rw[overloadable_in_APPEND])
  >- (
    imp_res_tac extends_APPEND_NIL
    >> imp_res_tac ConstDef_extends_not_overloadable
    >> fs[overloadable_in_def]
  )
  >> CCONTR_TAC
  >> fs[overloadable_in_def,MEM_SPLIT]
  >> rveq
  >> qpat_x_assum `_ extends _` (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC])
  >> imp_res_tac extends_APPEND_NIL
  >> fs[extends_NIL_CONS_extends,updates_cases]
QED

Theorem mk_bool_ctxt_extends_bool_ops_not_overloadable:
  !ctxt' ctxt. ctxt' ++ (mk_bool_ctxt ctxt) extends []
  ⇒ bool_ops_not_overloadable (ctxt' ++ mk_bool_ctxt ctxt)
Proof
  rw[holBoolSyntaxTheory.mk_bool_ctxt_def,holBoolSyntaxTheory.bool_ops_not_overloadable_def]
  >> rpt (CHANGED_TAC (TRY (match_mp_tac ConstDef_extends_not_overloadable')
    >> PURE_ONCE_REWRITE_TAC[INST_TYPE [alpha |-> ``:update``] CONS_APPEND]
    >> REWRITE_TAC[APPEND_ASSOC,APPEND_NIL]))
  >> pop_assum mp_tac
  >> fs[]
  >> rpt (CHANGED_TAC (
    PURE_ONCE_REWRITE_TAC[INST_TYPE [alpha |-> ``:update``] CONS_APPEND]
    >> REWRITE_TAC[APPEND_ASSOC,APPEND_NIL]))
  >> fs[overloadable_in_def,is_builtin_name_def]
QED

Theorem extends_is_bool_interpretation:
  is_set_theory ^mem ∧
    theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
    tysof(mk_bool_ctxt ctxt) ⊑ tyenv ∧ tmsof(mk_bool_ctxt ctxt) ⊑ tmenv ∧ axsof(mk_bool_ctxt ctxt) ⊆ axs ∧
    models δ γ ((tyenv,tmenv),axs) ⇒
    is_bool_interpretation_ext (tyenv,tmenv) δ γ
Proof
  strip_tac >>
  `models δ γ (thyof (mk_bool_ctxt ctxt))` by (
    match_mp_tac (UNDISCH models_reduce) >>
    imp_res_tac theory_ok_sig >> fs[] >>
    rpt(goal_assum drule) >>
    fs[theory_ok_def]) >>
  drule_all bool_has_bool_interpretation >>
  simp([is_bool_interpretation_ext_def,is_bool_interpretation_def,
      is_std_interpretation_total_fragment]) >>
  simp ints >>
  rpt(disch_then strip_assume_tac) >>
  simp[ext_term_frag_builtins_def] >>
  `FLOOKUP (tyenv) (strlit "bool") = SOME 0` by (
    drule_then match_mp_tac FLOOKUP_SUBMAP >>
    fs[theory_ok_def,is_std_sig_def]) >>
  `FLOOKUP (tyenv) (strlit "fun") = SOME 2` by (
    drule_then match_mp_tac FLOOKUP_SUBMAP >>
    fs[theory_ok_def,is_std_sig_def]) >>
  ntac 2 (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `models _ _ (thyof _)` kall_tac >>
  `is_std_sig (tyenv,tmenv)` by(fs[is_std_sig_def,theory_ok_def] >>
                                drule_then match_mp_tac FLOOKUP_SUBMAP >>
                                fs[]) >>
  `is_bool_sig (tyenv,tmenv)`
    by(rw([is_bool_sig_def] @ sigs) >>
       drule_then match_mp_tac FLOOKUP_SUBMAP >>
       rw[mk_bool_ctxt_def] >> EVAL_TAC) >>
  conj_asm1_tac
  >-
   (init_tac2 ``Const (strlit "!") (Fun (Fun A Bool) Bool)`` ``ForallDef`` ``ty:type`` exists_valuation >>
    fs[ForallDef_def,termsem_def] >> simp[Once ext_type_frag_builtins_def] >>
    imp_res_tac term_ok_welltyped >> fs[] >>
    simp[typeof_equation] >>
    qpat_abbrev_tac `a1 = ext_type_frag_builtins δ ty` >>
    PURE_ONCE_REWRITE_TAC [ext_type_frag_builtins_def] >> simp[] >>
    drule abstract_eq >> disch_then match_mp_tac >>
    simp[boolean_in_boolset] >>
    ntac 2 strip_tac >>
    conj_asm2_tac >- simp[boolean_in_boolset] >>
    drule((PURE_ONCE_REWRITE_RULE [termsem_ext_def] o GEN_ALL o MP_CANON) termsem_ext_equation) >>
    ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ av sigma` >>
    disch_then(qspecl_then [`sigma`,`av`,`P`,`Abs x True`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`sigma`,`av`] >>
    impl_tac >- (
      conj_tac >- (
        fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >> simp[Once ext_type_frag_builtins_def] >>
        CONV_TAC(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))) >>
        simp[]) >>
      fs[term_ok_clauses,bool_term_ok] >>
      conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[type_ok_def,ground_types_def,term_ok_clauses,bool_term_ok]
    ) >>
    simp[] >> disch_then kall_tac >>
    simp[termsem_def,combinTheory.UPDATE_def] >>
    simp[Once ext_type_frag_builtins_def] >>
    simp[holds_def] >>
    rw[boolean_def] >- (
      simp[true_neq_false] >> pop_assum mp_tac >> simp[] >>
      rw[] >> match_mp_tac apply_abstract_matchable >>
      simp[mem_boolset]
      ) >>
   simp[true_neq_false] >> qpat_x_assum `_ <> _` mp_tac >> simp[] >>
   drule in_funspace_abstract >> disch_then drule >>
   strip_tac >> rveq >>
   drule abstract_eq >> disch_then match_mp_tac >>
   rw[mem_boolset] >> metis_tac[apply_abstract])
  >-
   (init_tac2``Const (strlit "?") (Fun (Fun A Bool) Bool)`` ``ExistsDef`` ``ty:type`` exists_valuation >>
    fs[ExistsDef_def,termsem_def] >> simp[Once ext_type_frag_builtins_def] >>
    imp_res_tac term_ok_welltyped >> fs[] >>
    simp[typeof_equation] >>
    qpat_abbrev_tac `a1 = ext_type_frag_builtins δ ty` >>
    PURE_ONCE_REWRITE_TAC [ext_type_frag_builtins_def] >> simp[] >>
    simp[combinTheory.UPDATE_def] >>
    res_tac >>
    `Bool ∈ ground_types (tyenv,tmenv)` by(simp[ground_types_def,tyvars_def,type_ok_def]) >>
    first_x_assum drule >> simp[ext_term_frag_builtins_def,ext_type_frag_builtins_def] >> disch_then kall_tac >>
    drule abstract_eq >> disch_then match_mp_tac >>
    simp[boolean_in_boolset] >>
    ntac 2 strip_tac >>
    conj_asm2_tac >- simp[boolean_in_boolset] >>
    simp[ext_type_frag_builtins_def] >>
    qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand = _` >>
    drule apply_abstract >>
    disch_then(qspecl_then [`rator`,`rand`,`Funspace boolset boolset`,`boolset`] mp_tac) >>
    MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
    impl_tac >- (
      simp[boolean_in_boolset] >> match_mp_tac (MP_CANON abstract_in_funspace) >>
      rw[] >> match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      asm_exists_tac >> simp[] >>
      match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
      match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
      qexists_tac `Funspace a1 boolset` >> simp[] >>
      conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace) >>
      simp[]
      >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `boolset` >>
          rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
          metis_tac[]) >>
      simp[] >> metis_tac[boolean_in_boolset]
      ) >>
    simp[] >> disch_then kall_tac >>
    simp[boolean_eq_boolean] >>
    `inhabited a1`
      by(unabbrev_all_tac >> match_mp_tac(MP_CANON inhabited_ext) >>
         simp[] >> qexists_tac `FST(total_fragment(tyenv,tmenv))` >>
         fs[total_fragment_def,is_frag_interpretation_def,
            is_sig_fragment_def,is_type_frag_interpretation_def,ground_types_builtin_closure]) >>
    rename1 `e ⋲ a1` >> rename1 `ff ⋲ Funspace _ boolset` >>
    `ff ' e ⋲ boolset` by(metis_tac[apply_in_rng]) >>
    reverse EQ_TAC >- (
      rw[holds_def] >>
      drule apply_abstract >>
      qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
      disch_then(qspecl_then [`rator`,`rand`,`boolset`,`boolset`] mp_tac) >>
      MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
      impl_tac >- (
        simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
        asm_exists_tac >> simp[] >> match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
        match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
        qexists_tac `Funspace a1 boolset` >>
        conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace)
        >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
            simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            qexists_tac `boolset` >>
            rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
            metis_tac[]) >>
        simp[] >> metis_tac[boolean_in_boolset]) >>
      simp[] >> disch_then kall_tac >>
      qmatch_goalsub_abbrev_tac `_ ' b1 ' b2 = b3` >>
      drule(GEN_ALL apply_boolrel) >>
      disch_then(qspecl_then [`$==>`,`b1`,`b2`,`b3`] mp_tac) >>
      MAP_EVERY qunabbrev_tac [`b1`,`b2`,`b3`] >>
      impl_tac >- (
        conj_tac >- (
          match_mp_tac (MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `Funspace a1 boolset` >>
          conj_tac >> match_mp_tac (MP_CANON abstract_in_funspace)
          >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              qexists_tac `boolset` >> simp[mem_boolset] >>
              match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
              match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
              metis_tac[]) >>
          simp[] >> metis_tac[boolean_in_boolset]) >>
        simp[boolean_eq_true] >>
        qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
        drule apply_abstract >>
        disch_then(qspecl_then [`rator`,`rand`,`Funspace a1 boolset`,`boolset`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
        impl_tac >- (
          simp[boolean_in_boolset] >> match_mp_tac(MP_CANON abstract_in_funspace) >>
          rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          qexists_tac `boolset` >> simp[boolrel_in_funspace] >>
          metis_tac[apply_in_rng]) >>
        simp[boolean_eq_true] >> disch_then kall_tac >>
        disch_then drule >>
        drule apply_abstract >>
        qmatch_goalsub_abbrev_tac `Abstract _ _ rator ' rand` >>
        disch_then(qspecl_then [`rator`,`rand`,`a1`,`boolset`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`rator`,`rand`] >>
        impl_tac >- (
          simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
          asm_exists_tac >> simp[] >> match_mp_tac(MP_CANON apply_in_rng) >>
          simp[] >> qexists_tac `boolset` >> simp[boolrel_in_funspace,mem_boolset]) >>
        simp[] >> disch_then kall_tac >>
        qmatch_goalsub_abbrev_tac `_ ' b1 ' b2 = b3` >>
        drule(GEN_ALL apply_boolrel) >>
        disch_then(qspecl_then [`$==>`,`b1`,`b2`,`x''`] mp_tac) >>
        MAP_EVERY qunabbrev_tac [`b1`,`b2`,`b3`] >>
        impl_tac >- (rfs[mem_boolset,boolean_def,true_neq_false]) >>
        simp[]) >>
      simp[])
    >- (
      simp[holds_def] >>
      qmatch_goalsub_abbrev_tac`Abstract boolset boolset rator` >>
      drule apply_abstract >>
      disch_then(qspec_then `rator` mp_tac) >>
      disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
      disch_then(qspecl_then [`boolset`,`boolset`] mp_tac) >>
      `!x. x ⋲ boolset ==> rator x ⋲ boolset` by
       (qunabbrev_tac `rator` >> rw[] >> match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> asm_exists_tac >> simp[] >>
        match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `boolset` >>
        simp[boolrel_in_funspace] >>
        match_mp_tac(MP_CANON apply_in_rng) >>
        simp[] >> qexists_tac `Funspace a1 boolset` >>
        conj_tac >> match_mp_tac(MP_CANON abstract_in_funspace)
        >- (rw[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >> asm_exists_tac >>
            simp[] >> match_mp_tac(MP_CANON apply_in_rng) >> simp[] >>
            qexists_tac `boolset` >>
            rw[boolrel_in_funspace] >> match_mp_tac(MP_CANON apply_in_rng) >>
            metis_tac[]) >>
        simp[] >> metis_tac[boolean_in_boolset]) >>
      simp[] >> disch_then kall_tac >>
      qunabbrev_tac `rator` >> fs[] >>
      qho_match_abbrev_tac `(∀x. x ⋲ boolset ⇒ Boolrel R ' (Abstract d1 bs i1 ' (Abstract d2 bs (i2 x))) ' x = True) ==> _` >>
      `∀x. x <: boolset ⇒ Abstract d1 bs i1 ' (Abstract d2 bs (i2 x)) = i1 (Abstract d2 bs (i2 x))` by (
        rw[] >>
        match_mp_tac apply_abstract_matchable >>
        simp[Abbr`bs`,Abbr`d1`,Abbr`i1`,boolean_in_boolset] >>
        match_mp_tac (UNDISCH abstract_in_funspace) >>
        rw[Abbr`i2`] >>
        apply_abstract_tac ) >>
      simp[Abbr`R`,Abbr`bs`,Abbr`d2`] >>
      `∀x. (λm. i2 x m) = (i2 x)` by metis_tac[ETA_AX] >>
      `∀x a. x <: boolset /\ a <: a1 ⇒ Abstract a1 boolset (i2 x) ' a = i2 x a` by (
        rw[] >>
        match_mp_tac apply_abstract_matchable >>
        rw[Abbr`i2`] >>
        apply_abstract_tac ) >>
      simp[Abbr`i1`] >>
      simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true] >>
      simp[Abbr`i2`] >>
      `!x. x ⋲ a1 ==> ff ' x ⋲ boolset` by metis_tac[apply_in_rng] >>
      simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true] >>
      qunabbrev_tac `d1` >>
      ntac 7 (pop_assum kall_tac) >>
      metis_tac[mem_boolset,true_neq_false]))
QED

Theorem termsem_implies:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s p1 p2.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_implies_sig (tmsof s) ∧
    is_implies_interpretation(ext_term_frag_builtins (ext_type_frag_builtins δ) γ) ⇒
    termsem_ext δ γ v sigma (Implies p1 p2) =
    Boolean (termsem_ext δ γ v sigma p1 = True ⇒
             termsem_ext δ γ v sigma p2 = True)
Proof
  rw[termsem_def,termsem_ext_def,is_implies_sig_def,is_implies_interpretation_def] >>
  qmatch_goalsub_abbrev_tac `Boolrel _ ' tm1 ' tm2` >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  `tm1 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p1))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  `tm2 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p2))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  ntac 2 (pop_assum mp_tac) >>
  simp[] >> PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> rw[] >>
  simp[apply_boolrel_rw]
QED

Theorem termsem_forall:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s f y b.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_forall_sig (tmsof s) ∧
    is_forall_interpretation (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) (ext_type_frag_builtins δ) (TYPE_SUBSTf sigma y) ⇒
    termsem_ext δ γ v sigma (Forall f y b) =
    Boolean (∀x. x <: ext_type_frag_builtins δ (TYPE_SUBSTf sigma y) ⇒
                 termsem_ext δ γ (((f,y) =+ x) v) sigma b = True)
Proof
  rw[termsem_def,termsem_ext_def,is_implies_sig_def,is_forall_interpretation_def,
     ext_type_frag_builtins_simps] >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' rand` >>
  drule apply_abstract >>
  disch_then(qspecl_then [`rator`,`rand`,`dom`,`rng`] mp_tac) >>
  unabbrev_all_tac >>
  impl_tac >- (
    simp[boolean_in_boolset] >>
    match_mp_tac(MP_CANON abstract_in_funspace) >> simp[] >>
    rw[] >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ va` >>
    disch_then(qspecl_then [`va`,`sigma`,`b`] mp_tac) >>
    unabbrev_all_tac >>
    impl_tac >- (
      conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
      rw[] >> fs[combinTheory.UPDATE_def,valuates_frag_def] >>
      rw[] >> fs[] >> first_x_assum match_mp_tac >>
      imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
      rpt(disch_then drule) >> strip_tac >>
      drule term_frag_uninst_in_type_frag >> disch_then drule >>
      simp[]) >>
    simp[ext_type_frag_builtins_simps]) >>
  simp[boolean_eq_boolean] >> disch_then kall_tac >>
  simp[holds_def] >>
  ho_match_mp_tac ConseqConvTheory.forall_eq_thm >>
  rw[DECIDE ``!a b c. (a ==> b <=> a ==> c) = (a ==> (b <=> c))``] >>
  qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' rand` >>
  drule apply_abstract >>
  disch_then(qspecl_then [`rator`,`rand`,`dom`,`rng`] mp_tac) >>
  unabbrev_all_tac >>
  impl_tac >- (
    rw[] >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ va` >>
    disch_then(qspecl_then [`va`,`sigma`,`b`] mp_tac) >>
    unabbrev_all_tac >>
    impl_tac >- (
      conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
      rw[] >> fs[combinTheory.UPDATE_def,valuates_frag_def] >>
      rw[] >> fs[] >> first_x_assum match_mp_tac >>
      imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
      rpt(disch_then drule) >> strip_tac >>
      drule term_frag_uninst_in_type_frag >> disch_then drule >>
      simp[]) >>
    simp[ext_type_frag_builtins_simps]) >>
  simp[]
QED

Theorem termsem_exists:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s f y b.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_forall_sig (tmsof s) ∧
    is_exists_interpretation (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) (ext_type_frag_builtins δ) (TYPE_SUBSTf sigma y) ⇒
    termsem_ext δ γ v sigma (Exists f y b) =
    Boolean (∃x. x <: ext_type_frag_builtins δ (TYPE_SUBSTf sigma y) /\
                 termsem_ext δ γ (((f,y) =+ x) v) sigma b = True)
Proof
  rw[termsem_def,termsem_ext_def,is_implies_sig_def,is_exists_interpretation_def,
     ext_type_frag_builtins_simps] >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' rand` >>
  drule apply_abstract >>
  disch_then(qspecl_then [`rator`,`rand`,`dom`,`rng`] mp_tac) >>
  unabbrev_all_tac >>
  impl_tac >- (
    simp[boolean_in_boolset] >>
    match_mp_tac(MP_CANON abstract_in_funspace) >> simp[] >>
    rw[] >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule) >>
    qmatch_goalsub_abbrev_tac `termsem _ _ va` >>
    disch_then(qspecl_then [`va`,`sigma`,`b`] mp_tac) >>
    unabbrev_all_tac >>
    impl_tac >- (
      conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
      rw[] >> fs[combinTheory.UPDATE_def,valuates_frag_def] >>
      rw[] >> fs[] >> first_x_assum match_mp_tac >>
      imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
      rpt(disch_then drule) >> strip_tac >>
      drule term_frag_uninst_in_type_frag >> disch_then drule >>
      simp[]) >>
    simp[ext_type_frag_builtins_simps]) >>
  simp[boolean_eq_boolean] >> disch_then kall_tac >>
  simp[holds_def] >>
  qmatch_goalsub_abbrev_tac `Abstract dom rng rator ' _` >>
  drule apply_abstract >>
  disch_then(qspec_then `rator` mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
  disch_then(qspecl_then [`rng`,`dom`] mp_tac) >>
  `∀x. x ⋲ dom ==> rator x ⋲ rng`
    by(unabbrev_all_tac >> rw[] >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule) >>
       qmatch_goalsub_abbrev_tac `termsem _ _ va` >>
       disch_then(qspecl_then [`va`,`sigma`,`b`] mp_tac) >>
       unabbrev_all_tac >>
       impl_tac >- (
         conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
         rw[] >> fs[combinTheory.UPDATE_def,valuates_frag_def] >>
         rw[] >> fs[] >> first_x_assum match_mp_tac >>
         imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
         rpt(disch_then drule) >> strip_tac >>
         drule term_frag_uninst_in_type_frag >> disch_then drule >>
         simp[]) >>
       simp[ext_type_frag_builtins_simps]) >>
  metis_tac[]
QED

Theorem termsem_and:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s p1 p2.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_and_sig (tmsof s) ∧
    is_and_interpretation(ext_term_frag_builtins (ext_type_frag_builtins δ) γ) ⇒
    termsem_ext δ γ v sigma (And p1 p2) =
    Boolean (termsem_ext δ γ v sigma p1 = True /\
             termsem_ext δ γ v sigma p2 = True)
Proof
  rw[termsem_def,termsem_ext_def,is_and_sig_def,is_and_interpretation_def] >>
  qmatch_goalsub_abbrev_tac `Boolrel _ ' tm1 ' tm2` >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  `tm1 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p1))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  `tm2 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p2))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  ntac 2 (pop_assum mp_tac) >>
  simp[] >> PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> rw[] >>
  simp[apply_boolrel_rw]
QED

Theorem termsem_or:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s p1 p2.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_or_sig (tmsof s) ∧
    is_or_interpretation(ext_term_frag_builtins (ext_type_frag_builtins δ) γ) ⇒
    termsem_ext δ γ v sigma (Or p1 p2) =
    Boolean (termsem_ext δ γ v sigma p1 = True \/
             termsem_ext δ γ v sigma p2 = True)
Proof
  rw[termsem_def,termsem_ext_def,is_or_sig_def,is_or_interpretation_def] >>
  qmatch_goalsub_abbrev_tac `Boolrel _ ' tm1 ' tm2` >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  `tm1 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p1))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  `tm2 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p2))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  ntac 2 (pop_assum mp_tac) >>
  simp[] >> PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> rw[] >>
  simp[apply_boolrel_rw]
QED

Theorem termsem_not:
  is_set_theory ^mem ⇒
  ∀δ γ sigma v s p1 p2.
    is_frag_interpretation (total_fragment s) δ γ ∧
    valuates_frag(total_fragment s) δ v sigma ∧
    (∀ty. tyvars (sigma ty) = []) ∧
    (∀ty. type_ok (tysof s) (sigma ty)) ∧
    term_ok s p1 ∧
    typeof p1 = Bool ∧
    is_not_sig (tmsof s) ∧
    is_not_interpretation(ext_term_frag_builtins (ext_type_frag_builtins δ) γ) ⇒
    termsem_ext δ γ v sigma (Not p1) =
    Boolean (termsem_ext δ γ v sigma p1 ≠ True)
Proof
  rw[termsem_def,termsem_ext_def,is_not_sig_def,is_not_interpretation_def] >>
  qmatch_goalsub_abbrev_tac `_ ' tm1` >>
  qspec_then `s` assume_tac total_fragment_is_fragment >>
  `tm1 ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (typeof p1))`
    by(unabbrev_all_tac >>
       match_mp_tac termsem_in_type_ext2 >> rpt(asm_exists_tac >> simp[]) >>
       conj_asm1_tac >- metis_tac[terms_of_frag_uninst_term_ok] >>
       fs[valuates_frag_def] >> rw[] >> first_x_assum match_mp_tac >>
       imp_res_tac VFREE_IN_subterm >> drule subterm_in_term_frag_uninst >>
       rpt(disch_then drule) >> strip_tac >>
       drule term_frag_uninst_in_type_frag >> disch_then drule >>
       simp[]) >>
  ntac 2 (pop_assum mp_tac) >>
  simp[] >> PURE_ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> rw[] >>
  simp[apply_abstract,boolean_in_boolset]
QED

val _ = export_theory()
