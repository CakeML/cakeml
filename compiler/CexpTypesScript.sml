open HolKernel boolLib bossLib fmaptreeTheory finite_mapTheory pred_setTheory lcsymtacs
val _ = new_theory"CexpTypes"

(* applicative primitives with bytecode counterparts *)
val _ = Hol_datatype `
 Cprim1 = CRef | CDer`;
val _ = Hol_datatype `
 Cprim2 = CAdd | CSub | CMul | CDiv | CMod | CLt | CEq | CUpd`;

val _ = Hol_datatype `
 Cpat =
    CPvar of string
  | CPlit of lit
  | CPcon of num => Cpat list
  | CPref of Cpat`;

val _ = Hol_datatype `
 Cexp =
    CDecl of string list
  | CRaise of error
  | CHandle of Cexp => string => Cexp
  | CVar of string
  | CLit of lit
  | CCon of num => Cexp list
  | CTagEq of Cexp => num
  | CProj of Cexp => num
  | CLet of string => Cexp => Cexp
  | CLetfun of bool => string list => (string list # (Cexp + num)) list => Cexp
  | CFun of string list => (Cexp + num)
  | CCall of Cexp => Cexp list
  | CPrim1 of Cprim1 => Cexp
  | CPrim2 of Cprim2 => Cexp => Cexp
  | CIf of Cexp => Cexp => Cexp`;

val _ = Parse.type_abbrev("def",``:(string list # (Cexp + num))``)

(* and now the Cv type with its unnecessarily difficult recursion *)

val _ = Parse.overload_on("num_to_s0",``GENLIST (K (CHR 0))``)
val _ = Parse.overload_on("s0_to_num",``STRLEN``)

val b = ``:string``
val a = ``:lit +
num +
string list # def list # string +
num``
val Cv0 = ``:(^b,^a) fmaptree``
val _ = Parse.type_abbrev("Cv0",Cv0)
val Cvwf_def = new_specification("Cvwf_def",["Cvwf"],
fmtree_Axiom
|> Q.ISPEC
`λ^(mk_var("i",a)) ^(mk_var("fm",``:^b |-> (^b,^a) fmaptree``)) ^(mk_var("res",``:(^b,bool) fmap``)). (∀x. x ∈ FRANGE res ⇒ x) ∧
case i of
  | (INL l) => (fm = FEMPTY)
  | (INR (INL n)) => ∃vs. (fm = FUN_FMAP (combin$C EL vs o s0_to_num) (IMAGE num_to_s0 (count (LENGTH vs))))
  | (INR (INR (INL (ns,defs,d)))) => T
  | (INR (INR (INR n))) => (fm = FEMPTY)`)
val Cvs_exist = new_type_definition("Cv",
prove(
``∃v. Cvwf v``,
qexists_tac`FTNode (INL (Bool F)) FEMPTY` >>
rw[Cvwf_def]))

val Cv_bij_thm = define_new_type_bijections {
  ABS="toCv", REP="fromCv", name = "Cv_bij_thm", tyax = Cvs_exist}

val CLitv_def = Define`
  CLitv l = toCv (FTNode (INL l) FEMPTY)`
val CConv_def = Define`
  CConv n vs = toCv
    (FTNode (INR (INL n))
            (fromCv o_f FUN_FMAP (combin$C EL vs o s0_to_num) (IMAGE num_to_s0 (count (LENGTH vs)))))`
val CRecClos_def = Define`
  CRecClos env ns defs d = toCv
    (FTNode (INR (INR (INL (ns,defs,d))))
            (fromCv o_f env))`
val CLoc_def = Define`
  CLoc n = toCv (FTNode (INR (INR (INR n))) FEMPTY)`

val num_to_s0_inj = store_thm(
"num_to_s0_inj",
``∀x y. (num_to_s0 x = num_to_s0 y) = (x = y)``,
rpt gen_tac >>
reverse EQ_TAC >- rw[] >>
rw[listTheory.LIST_EQ_REWRITE])

val toCv_thm = store_thm(
"toCv_thm",
``Cvwf (FTNode i fm) ⇒
  (toCv (FTNode i fm) = case i of
   | INL l => CLitv l
   | INR (INL n) => CConv n (MAP toCv (GENLIST (FAPPLY fm o num_to_s0) (CARD (FDOM fm))))
   | INR (INR (INL (ns,defs,n))) => CRecClos (toCv o_f fm) ns defs n
   | INR (INR (INR n)) => CLoc n)``,
rw[Cvwf_def] >>
BasicProvers.EVERY_CASE_TAC >- (
  rw[CLitv_def] )
>- (
  rw[CConv_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  fs[FUN_FMAP_DEF,CARD_INJ_IMAGE,num_to_s0_inj] >>
  ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] >>
  conj_tac >- rw[] >>
  gen_tac >>
  simp_tac std_ss [FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
  strip_tac >>
  asm_simp_tac std_ss [o_f_FAPPLY,FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
  fs[rich_listTheory.EL_MAP] >> rw[] >>
  qmatch_assum_rename_tac `x < LENGTH vs`[] >>
  `num_to_s0 x ∈ IMAGE num_to_s0 (count (LENGTH vs))` by (rw[] >> PROVE_TAC[]) >>
  rw[FUN_FMAP_DEF] >>
  match_mp_tac EQ_SYM >>
  rw[GSYM (CONJUNCT2 Cv_bij_thm)] >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `num_to_s0 x` >>
  rw[FUN_FMAP_DEF] >>
  PROVE_TAC[])
>- (
  rw[CRecClos_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] >>
  rw[] >>
  match_mp_tac EQ_SYM >>
  rw[GSYM (CONJUNCT2 Cv_bij_thm)] >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `x` >>
  rw[] )
>- rw[CLoc_def])

val Cvwf_all_Cv = store_thm(
"Cvwf_all_Cv",
``(∀x. Cvwf x ⇒ P (toCv x)) ⇒ (∀v. P v)``,
metis_tac[Cv_bij_thm])

val Cvwf_thm = LIST_CONJ [
  SIMP_RULE (srw_ss())[](Q.SPEC`INL l`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INL n)`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INR (INL (ns,defs,n)))`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INR (INR n))`Cvwf_def)
]

val Cv_induction = store_thm(
"Cv_induction",
``∀P0 P1 P2.
(∀l. P0 (CLitv l)) ∧
(∀vs. P2 vs ⇒ ∀n. P0 (CConv n vs)) ∧
(∀env. P1 env ⇒ ∀ns defs d. P0 (CRecClos env ns defs d)) ∧
(∀env. (∀v. v ∈ FRANGE env ⇒ P0 v) ⇒ P1 env) ∧
(∀n. P0 (CLoc n)) ∧
(P2 []) ∧
(∀v vs. P0 v ∧ P2 vs ⇒ P2 (v::vs))
⇒
(∀v. P0 v) ∧ (∀env. P1 env) ∧ (∀vs. P2 vs)``,
rpt gen_tac >> strip_tac >>
reverse conj_asm1_tac >- (
  conj_tac >- (
    ho_match_mp_tac fmap_INDUCT >>
    rw[] ) >>
  Induct >> rw[]) >>
match_mp_tac Cvwf_all_Cv >>
ho_match_mp_tac ft_ind >>
rpt strip_tac >>
rw[toCv_thm] >>
BasicProvers.EVERY_CASE_TAC >- rw[] >>
TRY (rw[] >> NO_TAC) >>
first_x_assum match_mp_tac >- (
  `∀vs. EVERY P0 vs ⇒ P2 vs` by (Induct >> rw[]) >>
  pop_assum match_mp_tac >>
  rw[listTheory.EVERY_MAP,listTheory.EVERY_MEM,listTheory.MEM_GENLIST] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  qpat_assum `Cvwf X` mp_tac >>
  REWRITE_TAC [Cvwf_thm] >>
  strip_tac >>
  conj_tac >- (
    pop_assum SUBST_ALL_TAC >>
    qpat_assum `m < X` mp_tac >>
    simp_tac std_ss [FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
    simp_tac std_ss [IN_IMAGE,IN_COUNT] >>
    simp_tac std_ss [CARD_INJ_IMAGE,num_to_s0_inj,FINITE_COUNT,CARD_COUNT]) >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `num_to_s0 m` >>
  fs[FUN_FMAP_DEF,CARD_INJ_IMAGE,num_to_s0_inj] ) >>
first_assum match_mp_tac >>
fs[Cvwf_thm] >>
ONCE_REWRITE_TAC[FRANGE_DEF] >>
simp_tac(srw_ss())[] >>
simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
rpt strip_tac >>
qmatch_assum_rename_tac `k ∈ FDOM fm`[] >>
first_x_assum (qspec_then `k` (match_mp_tac o MP_CANON)) >>
rw[] >>
first_x_assum match_mp_tac >>
rw[FRANGE_DEF] >>
qexists_tac `k` >> rw[])

val toCv_o_fromCv = store_thm(
"toCv_o_fromCv",
``toCv o fromCv = I``,
rw[FUN_EQ_THM,Cv_bij_thm])
val _ = export_rewrites["toCv_o_fromCv"]

(* TODO: move? *)
val I_o_f = store_thm(
"I_o_f",
``I o_f fm = fm``,
rw[GSYM fmap_EQ_THM])
val _ = export_rewrites["I_o_f"]

val FEVERY_o_SND_FRANGE = store_thm(
"FEVERY_o_SND_FRANGE",
``∀P fm. FEVERY (P o SND) fm = ∀v. v ∈ FRANGE fm ⇒ P v``,
rpt gen_tac >> EQ_TAC >- (
  strip_tac >>
  rw[FRANGE_FLOOKUP] >>
  qsuff_tac `(P o SND) (k,v)` >- rw[] >>
  PROVE_TAC[FEVERY_FLOOKUP] ) >>
qid_spec_tac `fm` >>
ho_match_mp_tac fmap_INDUCT >>
rw[FEVERY_DEF,FAPPLY_FUPDATE_THM] >> rw[] >>
fsrw_tac[boolSimps.DNF_ss][FRANGE_DEF,DOMSUB_FAPPLY_THM])
val _ = export_rewrites["FEVERY_o_SND_FRANGE"]

(* this is no good
val o_f_cong = store_thm(
"o_f_cong",
``!f f' fm fm'.
(FDOM fm = FDOM fm') /\
(!x. x IN FDOM fm' ==> (f (fm ' x) = f' (fm' ' x)))
==> (f o_f fm = f' o_f fm')``,
SRW_TAC[][GSYM fmap_EQ_THM])
val _ = DefnBase.export_cong"o_f_cong"
*)

val Cvwf_fromCv = store_thm(
"Cvwf_fromCv",
``∀x. Cvwf (fromCv x)``,
METIS_TAC[Cv_bij_thm])
val _ = export_rewrites["Cvwf_fromCv"]

val Cvwf_o_fromCv = store_thm(
"Cvwf_o_fromCv",
``Cvwf o fromCv = K T``,
rw[FUN_EQ_THM])
val _ = export_rewrites["Cvwf_o_fromCv"]

val Cvwf_constructors = store_thm(
"Cvwf_constructors",
``(Cvwf ^(rand(rhs(concl(SPEC_ALL CLitv_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CConv_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CRecClos_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CLoc_def)))))``,
rw[Cvwf_def,FRANGE_DEF] >>
rw[o_f_FAPPLY] >>
qexists_tac `MAP fromCv vs` >>
rw[GSYM fmap_EQ_THM] >>
qmatch_abbrev_tac `X = FUN_FMAP x y ' z` >>
`z ∈ y` by (
  unabbrev_all_tac >> rw[] >> PROVE_TAC[] ) >>
unabbrev_all_tac >>
rw[FUN_FMAP_DEF,listTheory.EL_MAP] )
val _ = export_rewrites["Cvwf_constructors"]

val fromCv_thm = store_thm(
"fromCv_thm",``
(fromCv (CLitv l) = ^(rand(rhs(concl(SPEC_ALL CLitv_def))))) ∧
(fromCv (CConv n vs) = ^(rand(rhs(concl(SPEC_ALL CConv_def))))) ∧
(fromCv (CRecClos env ns defs d) = ^(rand(rhs(concl(SPEC_ALL CRecClos_def))))) ∧
(fromCv (CLoc n) = ^(rand(rhs(concl(SPEC_ALL CLoc_def)))))``,
rw[CLitv_def, CConv_def,  CRecClos_def, CLoc_def,
   GSYM (CONJUNCT2 Cv_bij_thm)])

val Cv_Axiom = store_thm(
"Cv_Axiom",
``∀f0 f1 f2 f3 f4 f5 f6 f7.
∃fn0 fn1 fn2.
(∀l. fn0 (CLitv l) = f0 l) ∧
(∀m vs. fn0 (CConv m vs) = f1 m vs (fn1 vs)) ∧
(∀env ns defs d. fn0 (CRecClos env ns defs d) = f3 env ns defs d (fn2 env)) ∧
(∀n. fn0 (CLoc n) = f4 n) ∧
(fn1 [] = f5) ∧
(∀v vs. fn1 (v::vs) = f6 v vs (fn0 v) (fn1 vs)) ∧
(∀env. fn2 env = f7 env (fn0 o_f env))``,
rw[] >>
qho_match_abbrev_tac `∃fn0. P fn0` >>
qsuff_tac `∃fn0. P (fn0 o fromCv)` >- PROVE_TAC[] >>
qunabbrev_tac `P` >>
fs[fromCv_thm] >>
qho_match_abbrev_tac `∃fn0 fn1 fn2. P fn0 fn1 fn2` >>
qsuff_tac `∃fn1 fn0. P fn0 (λvs. fn1 vs (MAP (fn0 o fromCv) vs)) (λenv. f7 env (fn0 o fromCv o_f env))` >- PROVE_TAC[] >>
Q.ISPECL_THEN [`λr0:α list. f5`,`λv vs r r0. f6 v vs (HD r0) (r (TL r0))`] strip_assume_tac listTheory.list_Axiom >>
qexists_tac `fn` >>
qunabbrev_tac `P` >>
fs[] >>
qexists_tac `fmtreerec
  (λi res fm.
    case i of
    | (INL l) => f0 l
    | (INR (INL m)) =>
      let vs =
        (MAP toCv (GENLIST (FAPPLY fm o num_to_s0) (CARD (FDOM fm))))
      in f1 m vs (fn vs (GENLIST (FAPPLY res o num_to_s0) (CARD (FDOM res))))
    | (INR (INR (INL (ns,defs,d)))) =>
      let env = toCv o_f fm in
      f3 env ns defs d (f7 env res)
    | (INR (INR (INR n))) => f4 n)` >>
rw[fmtreerec_thm,LET_THM] >>
rw[listTheory.MAP_GENLIST] >>
qmatch_abbrev_tac `f1 m vs' (fn vs' gl) = f1 m vs (fn vs ml)` >>
`vs' = vs` by (
  unabbrev_all_tac >>
  rw[listTheory.LIST_EQ_REWRITE,CARD_INJ_IMAGE,num_to_s0_inj] >>
  rw[Cv_bij_thm] >>
  qmatch_abbrev_tac `FUN_FMAP w y ' z = Z` >>
  `z ∈ y` by (
    unabbrev_all_tac >> rw[] >> PROVE_TAC[] ) >>
  unabbrev_all_tac >>
  rw[FUN_FMAP_DEF] ) >>
rw[] >>
AP_TERM_TAC >>
AP_TERM_TAC >>
unabbrev_all_tac >>
fs[CARD_INJ_IMAGE,num_to_s0_inj] >>
rw[listTheory.LIST_EQ_REWRITE,listTheory.EL_MAP] >>
AP_TERM_TAC >>
rw[Cv_bij_thm] >>
AP_TERM_TAC >>
qmatch_abbrev_tac `FUN_FMAP w y ' z = Z` >>
`z ∈ y` by (
  unabbrev_all_tac >> rw[] >> PROVE_TAC[] ) >>
unabbrev_all_tac >>
rw[FUN_FMAP_DEF] >>
rw[Cv_bij_thm])

val [Cv_case_def] = Prim_rec.define_case_constant Cv_Axiom

val Cv_11 = store_thm(
"Cv_11",``
(∀l1 l2.
  (CLitv l1 = CLitv l2) = (l1 = l2)) ∧
(∀m1 vs1 m2 vs2.
  (CConv m1 vs1 = CConv m2 vs2) = ((m1 = m2) ∧ (vs1 = vs2))) ∧
(∀env1 ns1 defs1 n1 env2 ns2 defs2 n2.
  (CRecClos env1 ns1 defs1 n1 = CRecClos env2 ns2 defs2 n2) =
  ((env1 = env2) ∧ (ns1 = ns2) ∧ (defs1 = defs2) ∧ (n1 = n2))) ∧
(∀n1 n2. (CLoc n1 = CLoc n2) = (n1 = n2))``,
conj_tac >- (
  rw[CLitv_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv r1 = toCv r2` >>
  `Cvwf r1 ∧ Cvwf r2` by (
    rw[Abbr`r1`,Abbr`r2`] ) >>
  `r1 = r2` by PROVE_TAC[Cv_bij_thm] >>
  unabbrev_all_tac >>
  fs[] ) >>
conj_tac >- (
  rw[CConv_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv r1 = toCv r2` >>
  `Cvwf r1 ∧ Cvwf r2` by (
    rw[Abbr`r1`,Abbr`r2`]  ) >>
  `r1 = r2` by PROVE_TAC[Cv_bij_thm] >>
  unabbrev_all_tac >>
  fsrw_tac[boolSimps.DNF_ss][GSYM fmap_EQ_THM] >>
  fs[IMAGE_11,num_to_s0_inj] >>
  rw[listTheory.LIST_EQ_REWRITE] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  `num_to_s0 x ∈ IMAGE num_to_s0 (count (LENGTH vs2))` by (
    rw[] >> PROVE_TAC[] ) >>
  rw[FUN_FMAP_DEF] >>
  PROVE_TAC[Cv_bij_thm] ) >>
conj_tac >- (
  rw[CRecClos_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv r1 = toCv r2` >>
  `Cvwf r1 ∧ Cvwf r2` by rw[Abbr`r1`,Abbr`r2`] >>
  `r1 = r2` by PROVE_TAC[Cv_bij_thm] >>
  unabbrev_all_tac >>
  fsrw_tac[boolSimps.DNF_ss][GSYM fmap_EQ_THM] >>
  pop_assum mp_tac >> rw[] >>
  PROVE_TAC[Cv_bij_thm] ) >> (
  rw[CLoc_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv r1 = toCv r2` >>
  `Cvwf r1 ∧ Cvwf r2` by (
    rw[Abbr`r1`,Abbr`r2`] ) >>
  `r1 = r2` by PROVE_TAC[Cv_bij_thm] >>
  unabbrev_all_tac >>
  fs[] ))
val _ = export_rewrites["Cv_11"]

val Cv_nice_ind = save_thm(
"Cv_nice_ind",
Cv_induction
|> Q.SPECL [`P`,`FEVERY (P o SND)`,`EVERY P`]
|> SIMP_RULE (srw_ss()) [FEVERY_FEMPTY,FEVERY_STRENGTHEN_THM]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN `P`)

val Cv_nchotomy = store_thm(
"Cv_nchotomy",
``∀Cv.
  (∃l. Cv = CLitv l) ∨
  (∃m vs. Cv = CConv m vs) ∨
  (∃env ns defs n. Cv = CRecClos env ns defs n) ∨
  (∃n. Cv = CLoc n)``,
ho_match_mp_tac Cv_nice_ind >> rw[])

val Cv_case_cong = save_thm(
"Cv_case_cong",
Prim_rec.case_cong_thm Cv_nchotomy Cv_case_def)
val _ = DefnBase.export_cong"Cv_case_cong"

val Cv_distinct = store_thm(
"Cv_distinct",
``(∀l m vs. CLitv l ≠ CConv m vs) ∧
  (∀l env ns defs n. CLitv l ≠ CRecClos env ns defs n) ∧
  (∀l n. CLitv l ≠ CLoc n) ∧
  (∀m vs env ns defs n. CConv m vs ≠ CRecClos env ns defs n) ∧
  (∀m vs n. CConv m vs ≠ CLoc n) ∧
  (∀env ns defs n m. CRecClos env ns defs n ≠ CLoc m)``,
rw[CLitv_def,CConv_def,CRecClos_def,CLoc_def] >>
qmatch_abbrev_tac `toCv r1 ≠ toCv r2` >>
(qsuff_tac `Cvwf r1 ∧ Cvwf r2 ∧ r1 ≠ r2` >- PROVE_TAC[Cv_bij_thm]) >>
unabbrev_all_tac >> fs[])
val _ = export_rewrites["Cv_distinct"]

val Cv_size_def =
Cv_Axiom
|> Q.ISPEC `λl. 1 + lit_size l`
|> Q.ISPEC `λm (vs : Cv list) (r:num). 1 + m + r`
|> Q.ISPEC `λ(env:string |-> Cv) xs b (r:num). 1 + r + list_size (list_size char_size) xs + Cexp_size b`
|> Q.ISPEC `λ(env:string |-> Cv) ns defs n r. 1 + r + list_size (list_size char_size) ns + list_size (pair_size (list_size (list_size char_size)) (sum_size Cexp_size I)) defs + list_size char_size n`
|> Q.ISPEC `λn:num. 1 + n`
|> Q.ISPEC `0:num`
|> Q.ISPEC `λv:Cv (vs : Cv list) (rv:num) rvs. 1 + rv + rvs`
|> Q.ISPEC `λ(env:string |-> Cv). fmap_size (list_size char_size) I`
|> SIMP_RULE(srw_ss())[]
|> (fn th => new_specification("Cv_size_def",["Cv_size","Cvs_size","Cv_env_size"],th))

val _ = TypeBase.write
  [TypeBasePure.mk_datatype_info
     {ax=TypeBasePure.ORIG Cv_Axiom,
      case_def=Cv_case_def,
      case_cong=Cv_case_cong,
      induction=TypeBasePure.ORIG Cv_induction,
      nchotomy=Cv_nchotomy,
      size=SOME (Parse.Term[QUOTE"Cv_size"],TypeBasePure.ORIG Cv_size_def),
      encode=NONE,
      fields=[], accessors=[], updates=[],
      recognizers = [],
      destructors = [],
      lift=NONE,
      one_one=SOME Cv_11,
      distinct=SOME Cv_distinct}];

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME(fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
S "val _ = TypeBase.write"                          ;NL();
S "  [TypeBasePure.mk_datatype_info"                ;NL();
S "     {ax=TypeBasePure.ORIG Cv_Axiom,"           ;NL();
S "      case_def=Cv_case_def,"                    ;NL();
S "      case_cong=Cv_case_cong,"                  ;NL();
S "      induction=TypeBasePure.ORIG Cv_induction,";NL();
S "      nchotomy=Cv_nchotomy,"                    ;NL();
S "      size=SOME (Parse.Term[QUOTE\"Cv_size\"],TypeBasePure.ORIG Cv_size_def),";NL();
S "      encode=NONE,"                              ;NL();
S "      fields=[], accessors=[], updates=[],"      ;NL();
S "      recognizers = [],"                         ;NL();
S "      destructors = [],"                         ;NL();
S "      lift=NONE,"                                ;NL();
S "      one_one=SOME Cv_11,"                      ;NL();
S "      distinct=SOME Cv_distinct}];"             ;NL()end)}

val _ = export_theory()
