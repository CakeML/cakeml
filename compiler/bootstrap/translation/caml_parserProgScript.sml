(*
  Translation of the functions in caml_parserScript.sml
 *)

open preamble camlPEGTheory camlPtreeConversionTheory caml_parserTheory;
open caml_lexProgTheory;
open ml_translatorLib ml_translatorTheory;

val _ = new_theory "caml_parserProg";

val _ = set_grammar_ancestry [
  "misc", "camlPEG", "camlPtreeConversion", "caml_parser",
  "ml_translator" ];

val _ = translation_extends "caml_lexProg";

val _ =
  temp_bring_to_front_overload "nType" {Name="nType", Thy="camlPEG"};
val _ =
  temp_bring_to_front_overload "nPattern" {Name="nPattern", Thy="camlPEG"};
val _ = temp_bring_to_front_overload "pegf" {Name="pegf", Thy="camlPEG"};
val _ = temp_bring_to_front_overload "seql" {Name="seql", Thy="camlPEG"};
val _ = temp_bring_to_front_overload "choicel" {Name="choicel", Thy="camlPEG"};
val _ = temp_bring_to_front_overload "pnt" {Name="pnt", Thy="camlPEG"};

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
fun preprocess def =
  def |> RW (!extra_preprocessing)
      |> CONV_RULE (DEPTH_CONV BETA_CONV)
      |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
      |> REWRITE_RULE [NOT_NIL_AND_LEMMA];

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
  val def = preprocess def
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = ml_translatorLib.use_string_type false;

val r = translate string_lt_def;

val _ = ml_translatorLib.use_string_type true;

(* -------------------------------------------------------------------------
 * Ptree conversion
 * ------------------------------------------------------------------------- *)

val r = translate FLAT;

Theorem bind_thm:
  bind x f = case x of INL err => INL err | INR y => f y
Proof
  Cases_on ‘x’ \\ rw [bind_def]
QED

val _ = extra_preprocessing :=
  [MEMBER_INTRO,MAP,bind_thm,ignore_bind_def,fail_def,return_def]

val _ = use_long_names := true;

val r = preprocess ptree_Op_def |> translate;

Theorem ptree_op_side[local]:
  ∀x. camlptreeconversion_ptree_op_side x
Proof
  rw [fetch "-" "camlptreeconversion_ptree_op_side_def"] \\ gs []
  \\ rename1 ‘isSymbol xx’ \\ Cases_on ‘xx’
  \\ gs [caml_lexTheory.destSymbol_def, caml_lexTheory.isSymbol_def]
QED

val _ = update_precondition ptree_op_side;

val r = preprocess ptree_Literal_def |> translate;


Theorem ptree_literal_side[local]:
  ∀x. camlptreeconversion_ptree_literal_side x
Proof
  rw [fetch "-" "camlptreeconversion_ptree_literal_side_def",
      caml_lexTheory.isInt_thm,
      caml_lexTheory.isChar_thm,
      caml_lexTheory.isString_thm] \\ gs []
QED

val _ = update_precondition ptree_literal_side;

val r = preprocess ptree_FieldName_def |> translate;

val r = translate (DefnBase.one_line_ify NONE precparserTheory.precparse_def)

Theorem precparse_side:
  ∀x y. precparser_precparse_side x y
Proof
  simp [FORALL_PROD]
  \\ ho_match_mp_tac precparserTheory.precparse_ind \\ rw []
  \\ rw [fetch "-" "precparser_precparse_side_def"] \\ gs []
  \\ Cases_on ‘stk0’ \\ Cases_on ‘strm0’ \\ gs [precparserTheory.isFinal_def]
  \\ Cases_on ‘h’ \\ gs [precparserTheory.isFinal_def,
                         fetch "-" "sum_outr_side_def"]
QED

val _ = update_precondition precparse_side;

val r = preprocess ptree_PPattern_def |> translate;

val r = preprocess ptree_Pattern_def |> translate;

(* This takes a long time.
 *)

val r = preprocess ptree_Expr_def |> translate;

Theorem ptree_Expr_preconds[local]:
  (∀x y. camlptreeconversion_ptree_expr_side x y) ∧
  (∀x. camlptreeconversion_ptree_letrecbinding_side x) ∧
  (∀x. camlptreeconversion_ptree_letrecbindings_side x) ∧
  (∀x. camlptreeconversion_ptree_letbinding_side x) ∧
  (∀x. camlptreeconversion_ptree_letbindings_side x) ∧
  (∀x. camlptreeconversion_ptree_patternmatches_side x) ∧
  (∀x. camlptreeconversion_ptree_patternmatch_side x) ∧
  (∀x. camlptreeconversion_ptree_exprlist_side x) ∧
  (∀x. camlptreeconversion_ptree_exprcommas_side x) ∧
  (∀x. camlptreeconversion_ptree_update_side x) ∧
  (∀x. camlptreeconversion_ptree_updates_side x)
Proof
  ho_match_mp_tac ptree_Expr_ind
  \\ strip_tac
  >- simp [Once (fetch "-" "camlptreeconversion_ptree_expr_side_def")]
  \\ strip_tac
  >- (
    reverse (Induct_on ‘nterm’) \\ gs []
    >- simp [Once (fetch "-" "camlptreeconversion_ptree_expr_side_def")]
    \\ qx_gen_tac ‘et’ \\ qx_gen_tac ‘nterm’
    \\ Cases_on ‘nterm ≠ et’ \\ gs []
    >- (
      rpt strip_tac
      \\ simp [Once (fetch "-" "camlptreeconversion_ptree_expr_side_def")])
    \\ simp [SF CONJ_ss]
    \\ rpt strip_tac
    \\ simp [Once (fetch "-" "camlptreeconversion_ptree_expr_side_def")]
    \\ rw [] \\ gs [caml_lexTheory.isSymbol_thm])
  \\ rw []
  \\ simp [Once (fetch "-" "camlptreeconversion_ptree_expr_side_def")]
QED

val _ = List.app (ignore o update_precondition) (CONJUNCTS ptree_Expr_preconds);


val r = translate partition_types_def;

Theorem camlptreeconversion_partition_types_side[local]:
  camlptreeconversion_partition_types_side x
Proof
  rw [fetch "-" "camlptreeconversion_partition_types_side_def",
      fetch "-" "sum_outl_side_def", fetch "-" "sum_outr_side_def"]
  \\ qpat_x_assum ‘PARTITION _ _ = _’ (assume_tac o SYM)
  \\ gs [PARTITION_DEF]
  \\ drule_then assume_tac PARTs_HAVE_PROP
  \\ gs [FORALL_PROD]
  \\ gs [EVERY_MEM, FORALL_PROD, quantHeuristicsTheory.ISR_exists,
         quantHeuristicsTheory.ISL_exists, SF SFY_ss]
  \\ strip_tac \\ gvs []
  \\ gs [SF DNF_ss, SF SFY_ss]
  \\ res_tac \\ fs []
QED

val _ = update_precondition camlptreeconversion_partition_types_side;

val r = translate sort_records_def;
val r = translate MAP_OUTR_def;
val r = translate extract_record_defns_def;
val r = translate strip_record_fields_def;

val r = preprocess ptree_TypeDefinition_def |> translate;

val r = preprocess ptree_ModuleType_def |> translate;
val r = preprocess ptree_Definition_def |> translate;

Theorem ptree_definition_side:
  (∀x. camlptreeconversion_ptree_definition_side x) ∧
  (∀x. camlptreeconversion_ptree_modexpr_side x) ∧
  (∀x. camlptreeconversion_ptree_moduleitems_side x) ∧
  (∀x. camlptreeconversion_ptree_moduleitem_side x) ∧
  (∀x. camlptreeconversion_ptree_exprordefn_side x)
Proof
  ho_match_mp_tac ptree_Definition_ind \\ rw []
  \\ simp [Once (fetch "-" "camlptreeconversion_ptree_definition_side_def")]
  \\ rw []
  \\ simp [parserProgTheory.parse_prog_side_def,
           parserProgTheory.peg_exec_side_def,
           parserProgTheory.coreloop_side_def]
  \\ rename [‘lexer_fun inp’]
  \\ qspec_then ‘lexer_fun inp’ strip_assume_tac
                cmlPEGTheory.owhile_TopLevelDecs_total
  \\ fs [parserProgTheory.INTRO_FLOOKUP, SF ETA_ss]
QED

val _ = List.map update_precondition (CONJUNCTS ptree_definition_side);

val r = preprocess ptree_Start_def |> translate;

(* -------------------------------------------------------------------------
 * Parser front-end
 * ------------------------------------------------------------------------- *)

val _ = extra_preprocessing := [MEMBER_INTRO,MAP]

Triviality and_or_imp_lemma:
  (b ∨ c ⇔ if b then T else c) ∧
  (b ∧ c ⇔ if b then c else F) ∧
  ((b ⇒ c) ⇔ if b then c else T) ∧
  ((if ~b then x else y) = if b then y else x)
Proof
  Cases_on ‘b’ \\ Cases_on ‘c’ \\ fs []
QED

val r = translate (identMixed_def |> PURE_REWRITE_RULE [and_or_imp_lemma]);

val r = translate run_lexer_def;
val r = translate run_parser_def;

Theorem run_parser_side[local]:
  ∀x. caml_parser_run_parser_side x
Proof
  rw [fetch "-" "caml_parser_run_parser_side_def",
      parserProgTheory.peg_exec_side_def,
      parserProgTheory.coreloop_side_def,
      camlPEGTheory.owhile_Start_total]
  \\ qspec_then ‘x’ strip_assume_tac owhile_Start_total
  \\ gs [parserProgTheory.INTRO_FLOOKUP, SF ETA_ss]
QED

val _ = update_precondition run_parser_side;

val r = translate run_def;

Theorem run_side[local]:
  ∀x. caml_parser_run_side x
Proof
  rw [fetch "-" "caml_parser_run_side_def", run_lexer_def]
QED

val _ = update_precondition run_side;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val () = ml_translatorLib.clean_on_exit := true;

val _ = export_theory ();
