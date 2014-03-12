open HolKernel boolLib bossLib lcsymtacs relationTheory pred_setTheory finite_mapTheory
open holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
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

val ConstDef_tac =
  pop_assum(assume_tac o REWRITE_RULE[GSYM extends_def]) >>
  match_mp_tac ConstDef_updates >>
  conj_asm1_tac >- (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`ctxt` >> simp[] ) >>
  conj_asm1_tac >- (
    imp_res_tac theory_ok_sig >>
    fs[term_ok_def,type_ok_def,term_ok_equation,FLOOKUP_UPDATE] >>
    simp[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
    simp[typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
    simp[tyvar_inst_exists] >>
    fs[is_std_sig_def] >> NO_TAC) >>
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

val bool_extends = store_thm("bool_extends",
  ``∀ctxt.
      theory_ok (thyof ctxt) ∧
      DISJOINT (FDOM (tmsof ctxt)) {"T";"F";"==>";"/\\";"\\/";"~";"!";"?"} ⇒
      mk_bool_ctxt ctxt extends ctxt``,
  REWRITE_TAC[mk_bool_ctxt_def] >>
  REWRITE_TAC[extends_def] >>
  ntac 2 strip_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >> disj2_tac >>
  conj_asm2_tac >- ConstDef_tac >>
  simp_tac (std_ss++listSimps.LIST_ss) [Once RTC_CASES1] >>
  conj_asm2_tac >- ConstDef_tac >>
  rw[Once RTC_CASES1])

val bool_extends_init = store_thm("bool_extends_init",
  ``mk_bool_ctxt init_ctxt extends init_ctxt``,
  match_mp_tac bool_extends >> simp[init_theory_ok] >>
  simp[init_ctxt_def])

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
