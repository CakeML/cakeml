open HolKernel boolLib bossLib lcsymtacs relationTheory listTheory pred_setTheory finite_mapTheory
open miscLib holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holBoolSyntax"

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
val Exists_def = ``AbsP (FAq (Implies (FAx (Implies (Comb P x) q)) q))``
val Or_def = ``Absp (Absq (FAr (Implies (Implies p r) (Implies (Implies q r) r))))``
val Falsity_def = ``FAp p``
val Not_def = ``Absp (Implies p Falsity)``
val mk_bool_ctxt_def = Define`
  mk_bool_ctxt ctxt =
    ConstDef "~" ^Not_def ::
    ConstDef "F" ^Falsity_def ::
    ConstDef "\\/" ^Or_def ::
    ConstDef "?" ^Exists_def ::
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

val _ = export_theory()
