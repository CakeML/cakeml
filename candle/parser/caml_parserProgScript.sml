(*
  Translation of the functions in caml_parserScript.sml
 *)

open preamble camlPEGTheory camlPtreeConversionTheory;
open caml_parserTheory caml_ptreeProgTheory;
open ml_translatorLib ml_translatorTheory;
open sexp_parserProgTheory;

val _ = new_theory "caml_parserProg";

val _ = set_grammar_ancestry [
  "misc", "camlPEG", "camlPtreeConversion", "caml_parser",
  "ml_translator" ];

val _ = translation_extends "sexp_parserProg";

val _ =
  temp_bring_to_front_overload "nType" {Name="nType", Thy="camlPEG"};
val _ =
  temp_bring_to_front_overload "nPattern" {Name="nPattern", Thy="camlPEG"};

(* -------------------------------------------------------------------------
 * Translator setup
 * ------------------------------------------------------------------------- *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
(*val _ = add_preferred_thy "termination";*)

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = ml_translatorLib.use_string_type true;

(* -------------------------------------------------------------------------
 * Parser front-end
 * ------------------------------------------------------------------------- *)

val r = translate find_next_newline_def;

Theorem find_next_newline_side[local]:
  ∀x y. find_next_newline_side x y
Proof
  ho_match_mp_tac find_next_newline_ind \\ rw []
  \\ simp [Once (fetch "-" "find_next_newline_side_def")]
QED

val _ = update_precondition find_next_newline_side;

val r = translate safe_substring_def;

Theorem safe_substring_side[local]:
  ∀x y z. safe_substring_side x y z
Proof
  rw [fetch "-" "safe_substring_side_def"]
QED

val _ = update_precondition safe_substring_side;

val r = translate get_nth_line_def;
val r = translate locs_to_string_def;
val r = translate run_parser_def;

(* TODO move these to the PEG script *)

Theorem frange_image[local]:
  FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)
Proof
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

val peg_range =
    SIMP_CONV (srw_ss())
              [FDOM_camlPEG, frange_image, camlpeg_rules_applied]
              “FRANGE camlPEG.rules”;

Theorem peg_start[local] = SIMP_CONV(srw_ss()) [camlPEG_def] “camlPEG.start”;

val wfpeg_rwts =
    pegTheory.wfpeg_cases
    |> ISPEC “camlPEG”
    |> (fn th => map (fn t => Q.SPEC t th)
                       [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                        `any f`, `empty v`, `not e v`, `rpt e f`,
                        `choicel []`, `choicel (h::t)`, `tokeq t`,
                        `pegf e f`, ‘tokSymP P’])
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                                            [choicel_def, seql_def,
                                             tokeq_def, tokSymP_def,
                                             pegf_def])));

val wfpeg_pnt =
    pegTheory.wfpeg_cases
    |> ISPEC “camlPEG”
    |> Q.SPEC ‘pnt n’
    |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts =
  pegTheory.peg0_cases
  |> ISPEC “camlPEG” |> CONJUNCTS
  |> map (fn th => map (fn t => Q.SPEC t th)
                       [`tok P f`, `choice e1 e2 f`,
                        ‘seq e1 e2 f’, ‘tokSymP P’,
                        `tokeq t`, `empty l`, `not e v`])
  |> List.concat
  |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                                          [tokeq_def, tokSymP_def])));

val pegfail_t = “pegfail”
val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end

val pegnt_case_ths =
    pegTheory.peg0_cases
    |> ISPEC “camlPEG” |> CONJUNCTS
    |> map (Q.SPEC ‘pnt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

Theorem peg0_pegf:
  peg0 G (pegf s f) = peg0 G s
Proof
  simp [pegf_def]
QED

Theorem peg0_seql:
  (peg0 G (seql [] f) ⇔ T) ∧
  (peg0 G (seql (h::t) f) ⇔ peg0 G h ∧ peg0 G (seql t I))
Proof
  simp[seql_def, peg0_pegf]
QED

Theorem peg0_tokeq:
  peg0 G (tokeq t) = F
Proof
  simp[tokeq_def]
QED

Theorem peg0_tokSymP[simp]:
  peg0 G (tokSymP P) ⇔ F
Proof
  simp[tokSymP_def]
QED

Theorem peg0_tokIdP[simp]:
  peg0 G (tokIdP P) ⇔ F
Proof
  simp[tokIdP_def]
QED

Theorem peg0_choicel:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

fun pegnt(t,acc) = let
  val th =
      Q.prove(`¬peg0 camlPEG (pnt ^t)`,
              simp pegnt_case_ths
              \\ simp [camlpeg_rules_applied]
              \\ simp [FDOM_camlPEG, pegf_def, seql_def, choicel_def,
                       peg_linfix_def, tokeq_def, try_def, pegf_def]
              \\ simp (peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val npeg0_rwts =
    List.foldl pegnt []
      [ “nShiftOp”, “nMultOp”, “nAddOp”, “nRelOp”, “nAndOp”, “nOrOp”,
        “nHolInfixOp”, “nCatOp”, “nPrefixOp”,
        “nValueName”, “nOperatorName”, “nConstrName”, “nTypeConstrName”,
        “nModuleName”, “nValuePath”, “nConstr”, “nTypeConstr”, “nModulePath”,
        “nLiteral”, “nIdent”, “nEList”, “nEConstr”, “nEBase”,
        “nELazy”, “nEAssert”, “nEFunapp”, “nEApp”, “nEPrefix”, “nENeg”,
        “nEShift”, “nEMult”, “nEAdd”, “nECons”, “nECat”, “nERel”, “nEAnd”,
        “nEOr”, “nEHolInfix”,
        “nEProd”, “nEIf”, “nESeq”, “nEMatch”, “nETry”, “nEFun”,
        “nEFunction”, “nELet”, “nELetRec”, “nEWhile”, “nEFor”, “nExpr”,
        “nLetBinding”, “nLetBindings”, “nLetRecBinding”, “nLetRecBindings”,
        “nPatternMatches”, “nPatternMatch”, “nTypeDefinition”, “nTypeDef”,
        “nTypeDefs”, “nTVar”, “nTAny”, “nTBase”, “nTConstr”, “nTProd”,
        “nTFun”, “nTAs”, “nType”, “nTypeList”, “nTypeLists”, “nTypeParams”,
        “nConstrDecl”, “nTypeReprs”, “nTypeRepr”, “nTypeInfo”, “nConstrArgs”,
        “nExcDefinition”, “nPAny”, “nPList”, “nPBase”, “nPLazy”, “nPConstr”,
        “nPApp”, “nPCons”, “nPProd”, “nPOr”, “nPAs”, “nPattern”, “nPatterns”,
        “nTopLet”, “nTopLetRec”, “nOpen”, “nSemis”, “nExprItem”, “nExprItems”,
        “nModuleDef”, “nDefinition”,  “nDefItem”, “nModExpr”, “nModuleItem” ];

fun wfnt(t,acc) = let
  val th =
    Q.prove(`wfpeg camlPEG (pnt ^t)`,
          SIMP_TAC (srw_ss())
                   [camlpeg_rules_applied ,
                    wfpeg_pnt, FDOM_camlPEG, try_def,
                    choicel_def, seql_def, tokIdP_def, identMixed_def,
                    tokeq_def, peg_linfix_def] THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts =
      [ “nShiftOp”, “nMultOp”, “nAddOp”, “nRelOp”, “nAndOp”, “nOrOp”,
        “nHolInfixOp”, “nCatOp”, “nPrefixOp”,
        “nValueName”, “nOperatorName”, “nConstrName”, “nTypeConstrName”,
        “nModuleName”, “nModulePath”, “nValuePath”, “nConstr”, “nTypeConstr”,
        “nLiteral”, “nIdent”, “nEList”, “nEConstr”, “nEBase”,
        “nELazy”, “nEAssert”, “nEFunapp”, “nEApp”, “nEPrefix”, “nENeg”,
        “nEShift”, “nEMult”, “nEAdd”, “nECons”, “nECat”, “nERel”, “nEAnd”,
        “nEOr”, “nEHolInfix”,
        “nEProd”, “nEIf”, “nESeq”, “nEMatch”, “nETry”, “nEFun”,
        “nEFunction”, “nELet”, “nELetRec”, “nEWhile”, “nEFor”, “nExpr”,
        “nPAny”, “nPList”, “nPBase”, “nPLazy”, “nPConstr”,
        “nPApp”, “nPCons”, “nPProd”, “nPOr”, “nPAs”, “nPattern”, “nPatterns”,
        “nLetBinding”, “nLetBindings”, “nLetRecBinding”, “nLetRecBindings”,
        “nPatternMatches”, “nPatternMatch”, “nTypeDefinition”,
        “nTVar”, “nTAny”, “nTBase”, “nTConstr”, “nTProd”, “nTFun”, “nTAs”,
        “nType”, “nTypeList”, “nTypeLists”, “nTypeParams”, “nTypeDef”,
        “nTypeDefs”, “nConstrDecl”, “nTypeReprs”, “nTypeRepr”, “nTypeInfo”,
        “nConstrArgs”, “nExcDefinition”, “nTopLet”, “nTopLetRec”, “nOpen”,
        “nSemis”, “nExprItem”, “nExprItems”, “nModuleDef”, “nModExpr”,
        “nDefinition”, “nDefItem”, “nModuleItem”, “nModuleItems”, “nStart”];

val cml_wfpeg_thm = save_thm(
  "cml_wfpeg_thm",
  LIST_CONJ (List.foldl wfnt [] topo_nts))

val subexprs_pnt = Q.prove(
  `subexprs (pnt n) = {pnt n}`,
  simp [pegTheory.subexprs_def, pnt_def]);

Theorem PEG_exprs =
   “Gexprs camlPEG”
  |> SIMP_CONV (srw_ss())
       [pegTheory.Gexprs_def, pegTheory.subexprs_def, peg_range,
        try_def, tokeq_def, seql_def, pegf_def, choicel_def,
        sumID_def,
        subexprs_pnt, peg_start, INSERT_UNION_EQ ];

Theorem PEG_wellformed[simp]:
   wfG camlPEG
Proof
  simp [pegTheory.wfG_def, pegTheory.Gexprs_def, pegTheory.subexprs_def,
        subexprs_pnt, peg_start, peg_range, DISJ_IMP_THM, FORALL_AND_THM,
        choicel_def, seql_def, pegf_def, tokeq_def, try_def,
        peg_linfix_def, tokSymP_def, tokIdP_def]
  \\ simp (cml_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts)
QED

Theorem parse_Start_total =
  MATCH_MP pegexecTheory.peg_exec_total PEG_wellformed
  |> REWRITE_RULE [peg_start]
  |> Q.GEN `i`;

Theorem coreloop_Start_total =
  MATCH_MP pegexecTheory.coreloop_total PEG_wellformed
  |> REWRITE_RULE [peg_start]
  |> Q.GEN `i`;

Theorem owhile_Start_total =
  SIMP_RULE (srw_ss()) [pegexecTheory.coreloop_def] coreloop_Start_total;

Theorem run_parser_side[local]:
  ∀x. run_parser_side x
Proof
  rw [fetch "-" "run_parser_side_def", peg_exec_side_def, coreloop_side_def]
  \\ qspec_then ‘x’ strip_assume_tac owhile_Start_total
  \\ gs [INTRO_FLOOKUP, SF ETA_ss]
QED

val _ = update_precondition run_parser_side;

val r = translate run_def;

Theorem run_side[local]:
  ∀x. run_side x
Proof
  rw [fetch "-" "run_side_def", run_lexer_def]
QED

val _ = update_precondition run_side;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val () = ml_translatorLib.clean_on_exit := true;

val _ = export_theory ();

