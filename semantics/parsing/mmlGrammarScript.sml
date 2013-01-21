open HolKernel Parse boolLib bossLib

open TokensTheory grammarTheory

val _ = new_theory "mmlGrammar"

(* miniml finite token *)
val _ = Hol_datatype`
  mftok0 = mfLpar | mfRpar | mfStar | mfComma | mfArrow
         | mfSemicolon | mfEquals | mfDarrow | mfLbrack | mfRbrack
         | mfUnderbar | mfLbrace | mfRbrace | mfBar | mfAnd
         | mfAndalso | mfOrelse | mfCase | mfType | mfElse | mfIf
         | mfFn | mfLet | mfFun | mfIn | mfEnd | mfPlus | mfMinus
         | mfDivides | mfCons | mfLess | mfNeq | mfID | mfConName
         | mfInteger | mfTrue | mfFalse | mfError
`;

local
  open pred_setTheory
  val in_insert' =
      pred_setTheory.IN_INSERT
        |> GSYM
        |> SIMP_RULE bool_ss [IN_DEF, SimpLHS]
  val lamin = prove(
    ``(\a. a IN s) = s``,
    SRW_TAC [][pred_setTheory.EXTENSION, pred_setTheory.IN_ABS])
  val lamsing = prove(
    ``(\a. a = x) = {x}``,
    SRW_TAC [][pred_setTheory.EXTENSION, pred_setTheory.IN_ABS])
  val a = mk_var("a", ``:mftok0``)
in
val univ_mftok0 = save_thm(
  "univ_mftok0",
  TypeBase.nchotomy_of ``:mftok0``
       |> SPEC_ALL
       |> SIMP_RULE bool_ss [in_insert', lamin, lamsing]
       |> EQT_INTRO
       |> SYM
       |> TRANS (IN_UNIV |> ISPECL[a] |> EQT_INTRO)
       |> GEN a
       |> CONV_RULE (REWR_CONV (GSYM EXTENSION)));
val finite_univ_mftok0 = store_thm(
  "finite_univ_mftok0",
  ``FINITE univ(:mftok0)``,
  SIMP_TAC (srw_ss()) [univ_mftok0]);
val _ = export_rewrites ["finite_univ_mftok0"]
end

val _ = type_abbrev("mftok", ``:mftok0 finite_image``)
val _ = overload_on("mkTok", ``mk_finite_image``)

val mkTok_inverse =
    fcpTheory.finite_image_tybij |> CONJUNCT2 |> SPEC_ALL |> EQ_IMP_RULE |> #1
                                 |> BETA_RULE
                                 |> REWRITE_RULE [ASSUME ``FINITE univ(:'a)``]
                                 |> DISCH_ALL


val mkTok_11 = store_thm(
  "mkTok_11",
  ``mkTok (x:mftok0) = mkTok y ⇔ x = y``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN
  DISCH_THEN (MP_TAC o Q.AP_TERM `dest_finite_image`) THEN
  ASM_SIMP_TAC (srw_ss()) [mkTok_inverse]);
val _ = export_rewrites ["mkTok_11"]

val mfCategorise_def = Define`
  mfCategorise LparT = mfLpar ∧
  mfCategorise RparT = mfRpar ∧
  mfCategorise StarT = mfStar ∧
  mfCategorise CommaT = mfComma ∧
  mfCategorise ArrowT = mfArrow ∧
  mfCategorise SemicolonT = mfSemicolon ∧
  mfCategorise EqualsT = mfEquals ∧
  mfCategorise DarrowT = mfDarrow ∧
  mfCategorise LbrackT = mfLbrack ∧
  mfCategorise RbrackT = mfRbrack ∧
  mfCategorise UnderbarT = mfUnderbar ∧
  mfCategorise LbraceT = mfLbrace ∧
  mfCategorise RbraceT = mfRbrace ∧
  mfCategorise BarT = mfBar ∧
  mfCategorise AndT = mfAnd ∧
  mfCategorise AndalsoT = mfAndalso ∧
  mfCategorise OrelseT = mfOrelse ∧
  mfCategorise CaseT = mfCase ∧
  mfCategorise TypeT = mfType ∧
  mfCategorise ElseT = mfElse ∧
  mfCategorise IfT = mfIf ∧
  mfCategorise FnT = mfFn ∧
  mfCategorise LetT = mfLet ∧
  mfCategorise FunT = mfFun ∧
  mfCategorise InT = mfIn ∧
  mfCategorise EndT = mfEnd ∧
(*   mfCategorise MinusT = mfMinus ∧
  mfCategorise DividesT = mfDivides ∧
  mfCategorise ConsT = mfCons ∧
  mfCategorise LessT = mfLess ∧
  mfCategorise NeqT = mfNeq ∧
  mfCategorise IDT = mfID ∧
  mfCategorise ConNameT = mfConName ∧
  mfCategorise TrueT = mfTrue ∧
  mfCategorise FalseT = mfFalse ∧ *)
  mfCategorise (IntT i) = mfInteger ∧
  mfCategorise _ = mfError`

val _ = export_theory()
