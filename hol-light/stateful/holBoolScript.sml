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
val mk_bool_ctxt_def = Define`
  mk_bool_ctxt ctxt =
    ConstDef "~" (Absp (Implies p Falsity)) ::
    ConstDef "F" (FAp p) ::
    ConstDef "\\/" (Absp (Absq (FAr (Implies (Implies p r) (Implies (Implies q r) r))))) ::
    ConstDef "?" (AbsP (FAq (Implies (FAx (Implies (Comb P x) q)) q))) ::
    ConstDef "!" (AbsP (P === Absx Truth)) ::
    ConstDef "==>" (Absp (Absq (And p q === p))) ::
    ConstDef "/\\"
      (Absp (Absq (Absf (Comb (Comb f p) q) ===
                   Absf (Comb (Comb f Truth) Truth)))) ::
    ConstDef "T" (Absp p === Absp p) ::
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

open holSemanticsTheory

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
  qabbrev_tac`thy = thyof ctx` >>
  qabbrev_tac`sig = sigof ctx` >>
  imp_res_tac theory_ok_sig >>
  `FLOOKUP (tysof sig) "bool" = SOME 0` by (
    pop_assum mp_tac >>
    simp[is_std_sig_def,Abbr`sig`,Abbr`ctx`,Abbr`thy`])
  conj_asm1_tac >- (
    fs[models_def] >>
    first_x_assum(qspec_then`Const "T" Bool === (Absp p === Absp p)`mp_tac) >>
    discharge_hyps >- (unabbrev_all_tac >> EVAL_TAC) >>
    simp[satisfies_def] >>
    qspecl_then[`tysof thy`,`tyaof i`]mp_tac (UNDISCH valuation_exists) >>
    discharge_hyps >- fs[is_interpretation_def] >> strip_tac >>
    disch_then(qspec_then`v`mp_tac) >> simp[] >>
    `is_structure (sigof thy) i v` by fs[is_structure_def] >>
    `term_ok (sigof thy) (Truth === Absp p === Absp p)` by (
      fs[Abbr`thy`,term_ok_equation,term_ok_def,type_ok_def,Abbr`sig`,Abbr`ctx`
        ,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
      EVAL_TAC >> simp[]) >>
    `term_ok (sigof (mk_bool_ctxt ctxt)) (Absp p === Absp p)` by (
      unabbrev_all_tac >>
      fs[term_ok_equation,term_ok_def,type_ok_def
        ,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL] ) >>
    rfs[Abbr`thy`,Abbr`sig`,termsem_equation,boolean_eq_true,termsem_def] >>
    qspecl_then[`sigof ctx`,`i`,`"T"`,`Bool`,`Bool`,`[]`]mp_tac instance_def >>
    simp[Abbr`ctx`] >>
    discharge_hyps >- EVAL_TAC >> simp[tyvars_def]
    is_std_interpretation_def
*)

(*
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
