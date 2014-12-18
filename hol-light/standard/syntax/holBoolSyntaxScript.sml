open HolKernel boolLib bossLib lcsymtacs relationTheory listTheory pred_setTheory finite_mapTheory alistTheory pairTheory
open miscLib holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holBoolSyntax"

val _ = Parse.overload_on("True",``Const (strlit "T") Bool``)
val _ = Parse.overload_on("And",``λp1 p2. Comb (Comb (Const (strlit "/\\") (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Implies",``λp1 p2. Comb (Comb (Const (strlit "==>") (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Forall",``λx ty p. Comb (Const (strlit "!") (Fun (Fun ty Bool) Bool)) (Abs (Var x ty) p)``)
val _ = Parse.overload_on("Exists",``λx ty p. Comb (Const (strlit "?") (Fun (Fun ty Bool) Bool)) (Abs (Var x ty) p)``)
val _ = Parse.overload_on("Or",``λp1 p2. Comb (Comb (Const (strlit "\\/") (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("False",``Const (strlit "F") Bool``)
val _ = Parse.overload_on("Not",``λp. Comb (Const (strlit "~") (Fun Bool Bool)) p``)

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
val TrueDef_def = Define`TrueDef = Abs p p === Abs p p`
val AndDef_def = Define`AndDef = Abs p (Abs q (Abs f (Comb (Comb f p) q) === Abs f (Comb (Comb f True) True)))`
val ImpliesDef_def = Define`ImpliesDef = Abs p (Abs q (And p q === p))`
val ForallDef_def = Define`ForallDef = Abs P (P === Abs x True)`
val ExistsDef_def = Define`ExistsDef = Abs P (FAq (Implies (FAx (Implies (Comb P x) q)) q))`
val OrDef_def = Define`OrDef = Abs p (Abs q (FAr (Implies (Implies p r) (Implies (Implies q r) r))))`
val FalseDef_def = Define`FalseDef = FAp p`
val NotDef_def = Define`NotDef = Abs p (Implies p False)`
val Defs = [TrueDef_def, AndDef_def, ImpliesDef_def, ForallDef_def, ExistsDef_def, OrDef_def, FalseDef_def, NotDef_def]
val mk_bool_ctxt_def = Define`
  mk_bool_ctxt ctxt =
    ConstDef (strlit "~") NotDef ::
    ConstDef (strlit "F") FalseDef ::
    ConstDef (strlit "\\/") OrDef ::
    ConstDef (strlit "?") ExistsDef ::
    ConstDef (strlit "!") ForallDef ::
    ConstDef (strlit "==>") ImpliesDef ::
    ConstDef (strlit "/\\") AndDef ::
    ConstDef (strlit "T")  TrueDef ::
    ctxt`

(* bool is a good extension *)

val term_ok_clauses = store_thm("term_ok_clauses",
  ``is_std_sig sig ⇒
    (term_ok sig (Var s ty) ⇔ type_ok (tysof sig) ty) ∧
    (type_ok (tysof sig) (Tyvar a) ⇔ T) ∧
    (type_ok (tysof sig) Bool ⇔ T) ∧
    (type_ok (tysof sig) (Fun ty1 ty2) ⇔ type_ok (tysof sig) ty1 ∧ type_ok (tysof sig) ty2) ∧
    (term_ok sig (Comb t1 t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ welltyped (Comb t1 t2)) ∧
    (term_ok sig (t1 === t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ typeof t1 = typeof t2) ∧
    (term_ok sig (Abs (Var s ty) t) ⇔ type_ok (tysof sig) ty ∧ term_ok sig t)``,
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
      DISJOINT (FDOM (tmsof ctxt)) (IMAGE strlit {"T";"F";"==>";"/\\";"\\/";"~";"!";"?"}) ⇒
      mk_bool_ctxt ctxt extends ctxt``,
  REWRITE_TAC(mk_bool_ctxt_def::Defs) >>
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

(* signatures of Boolean constants *)

val is_true_sig_def = Define`
  is_true_sig tmsig ⇔ FLOOKUP tmsig (strlit "T") = SOME Bool`
val is_false_sig_def = Define`
  is_false_sig tmsig ⇔ FLOOKUP tmsig (strlit "F") = SOME Bool`
val is_implies_sig_def = Define`
  is_implies_sig tmsig ⇔ FLOOKUP tmsig (strlit "==>") = SOME (Fun Bool (Fun Bool Bool))`
val is_and_sig_def = Define`
  is_and_sig tmsig ⇔ FLOOKUP tmsig (strlit "/\\") = SOME (Fun Bool (Fun Bool Bool))`
val is_or_sig_def = Define`
  is_or_sig tmsig ⇔ FLOOKUP tmsig (strlit "\\/") = SOME (Fun Bool (Fun Bool Bool))`
val is_not_sig_def = Define`
  is_not_sig tmsig ⇔ FLOOKUP tmsig (strlit "~") = SOME (Fun Bool Bool)`
val is_forall_sig_def = Define`
  is_forall_sig tmsig ⇔ FLOOKUP tmsig (strlit "!") = SOME (Fun (Fun A Bool) Bool)`
val is_exists_sig_def = Define`
  is_exists_sig tmsig ⇔ FLOOKUP tmsig (strlit "?") = SOME (Fun (Fun A Bool) Bool)`
val sigs = [is_true_sig_def, is_false_sig_def, is_implies_sig_def, is_and_sig_def,
            is_or_sig_def, is_not_sig_def, is_forall_sig_def, is_exists_sig_def]

val is_bool_sig_def = Define`
  is_bool_sig (sig:sig) ⇔
  is_std_sig sig ∧
  is_true_sig (tmsof sig) ∧
  is_false_sig (tmsof sig) ∧
  is_implies_sig (tmsof sig) ∧
  is_and_sig (tmsof sig) ∧
  is_or_sig (tmsof sig) ∧
  is_not_sig (tmsof sig) ∧
  is_forall_sig (tmsof sig) ∧
  is_exists_sig (tmsof sig)`

val bool_has_bool_sig = store_thm("bool_has_bool_sig",
  ``∀ctxt. is_std_sig (sigof ctxt)
  ⇒ is_bool_sig (sigof (mk_bool_ctxt ctxt))``,
  rw[is_bool_sig_def] >- (
    fs[is_std_sig_def,mk_bool_ctxt_def,FLOOKUP_UPDATE] ) >>
  EVAL_TAC)

val is_bool_sig_std = store_thm("is_bool_sig_std",
  ``is_bool_sig sig ⇒ is_std_sig sig``, rw[is_bool_sig_def])

val is_bool_sig_extends = store_thm("is_bool_sig_extends",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_bool_sig (sigof ctxt1) ⇒ is_bool_sig (sigof ctxt2)``,
  ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  conj_tac >- rw[is_bool_sig_def] >>
  conj_tac >- (
    simp[is_bool_sig_def,is_std_sig_def] >>
    simp sigs >> rw[] >>
    rw[FLOOKUP_UPDATE] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[is_bool_sig_def,is_std_sig_def] >>
    fs sigs >>
    rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[is_bool_sig_def,is_std_sig_def] >>
    rw[FLOOKUP_UPDATE] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  rw[is_bool_sig_def,is_std_sig_def] >>
  fs sigs >>
  rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD] >>
  metis_tac[] )

(* Boolean terms are ok *)

val bool_term_ok = store_thm("bool_term_ok",
  ``∀sig. is_bool_sig sig ⇒
    term_ok sig True ∧
    (∀p1 p2. term_ok sig (And p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    (∀p1 p2. term_ok sig (Implies p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    (∀z ty p. term_ok sig (Forall z ty p) ⇔ type_ok (tysof sig) ty ∧ term_ok sig p ∧ typeof p = Bool) ∧
    (∀z ty p. term_ok sig (Exists z ty p) ⇔ type_ok (tysof sig) ty ∧ term_ok sig p ∧ typeof p = Bool) ∧
    (∀p1 p2. term_ok sig (Or p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    term_ok sig False ∧
    (∀p. term_ok sig (Not p) ⇔ term_ok sig p ∧ typeof p = Bool)``,
  rw[] >> imp_res_tac is_bool_sig_std >> rw[term_ok_clauses] >>
  rw[term_ok_def] >> fs[is_bool_sig_def] >> fs sigs >> rw[term_ok_clauses,tyvar_inst_exists] >>
  PROVE_TAC[term_ok_welltyped])

val _ = export_theory()
