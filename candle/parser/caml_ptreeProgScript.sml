(*
  Translation of the functions in camlPEGScript.sml and
  camlPtreeConversionScript.sm
 *)

open preamble camlPEGTheory camlPtreeConversionTheory;
open camlPtreeConversionTheory caml_lexProgTheory;
open ml_translatorLib ml_monad_translatorLib ml_translatorTheory;

val _ = new_theory "caml_ptreeProg";

val _ = translation_extends "caml_lexProg";

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
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = ml_translatorLib.use_string_type true;

(* -------------------------------------------------------------------------
 * PEG stuff
 * ------------------------------------------------------------------------- *)

val r = register_type “:('a,'b,'c) parsetree”;
val r = register_type “:('a,'b,'c,'d) peg”;
val r = register_type “:camlNT”;

Theorem locnle:
  locnle x y =
    case (x,y) of
    | (UNKNOWNpt,_) => T
    | (_,EOFpt) => T
    | (POSN x1 x2,POSN y1 y2) => ((x1 < y1) ∨ (x1 = y1) ∧ (x2 ≤ y2))
    | _ => F
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs []
  \\ fs [locationTheory.locnle_def] \\ EVAL_TAC \\ fs []
QED

val r = translate locnle;

val r = translate camlPEG_def;

Theorem INTRO_FLOOKUP:
   (if n ∈ FDOM G.rules then
      pegexec$EV (G.rules ' n) i r eo errs (appf1 tf3 k) fk
    else Looped) =
   (case FLOOKUP G.rules n of
      NONE => Looped
    | SOME x => pegexec$EV x i r eo errs (appf1 tf3 k) fk)
Proof
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]
QED

val r = translate (def_of_const “coreloop” |> RW [INTRO_FLOOKUP]
                   |> SPEC_ALL |> RW1 [FUN_EQ_THM]);

val r = translate (def_of_const “peg_exec”);

(* -------------------------------------------------------------------------
 * Ptree conversion
 * ------------------------------------------------------------------------- *)

val _ = use_full_type_names := false;

val _ = register_exn_type “:caml_ptree_exn”;
val CAML_PTREE_EXN_TYPE_def = theorem "CAML_PTREE_EXN_TYPE_def";

val _ = use_full_type_names := true;

(* Initialize the monadic translator *)

val (monad_parameters, exn_specs) =
  start_dynamic_init_fixed_store_translation
    [("dummy", get_dummy_def, set_dummy_def)]
    [] []             (* Ref-, resizable array- and fixed-size array names *)
    "CAML_PTREE_STORE"   (* hprop name *)
    “:caml_ptree_state”  (* state type *)
    CAML_PTREE_EXN_TYPE_def
    [(raise_Fail_def, handle_Fail_def)]
    []                   (* Additional thys for types *)
    NONE;                (* store_pinv_def_opt *)

(* Translate ptree conversion into code that can raise exceptions *)

val r = translate grammarTheory.destTOK_def;
val r = m_translate option_def;
val r = m_translate destLf_def;
val r = m_translate ptree_Op_def;

Theorem ptree_op_side[local]:
  ∀x s. ptree_op_side s x
Proof
  rw [fetch "-" "ptree_op_side_def"] \\ gs []
  \\ rename1 ‘isSymbol xx’ \\ Cases_on ‘xx’
  \\ gs [caml_lexTheory.destSymbol_def, caml_lexTheory.isSymbol_def]
QED

val _ = update_local_precondition ptree_op_side;

val r = m_translate ptree_Literal_def;

Theorem ptree_literal_side[local]:
  ∀s x. ptree_literal_side s x
Proof
  rw [fetch "-" "ptree_literal_side_def",
      caml_lexTheory.isInt_thm,
      caml_lexTheory.isChar_thm,
      caml_lexTheory.isString_thm] \\ gs []
QED

val _ = update_local_precondition ptree_literal_side;

(* TODO: Bug in the translator makes this fail when tk is returned *)

Theorem expect_tok_alt:
  ∀symb token.
    expect_tok symb token =
      do (s,l) <- destLf symb;
         tk <- option (destTOK (s,l));
         if tk = token then
           st_ex_return token
         else
           raise_Fail l «Unexpected token»
      od
Proof
  rw [expect_tok_def, ELIM_UNCURRY]
QED

val r = m_translate expect_tok_alt;

val r = translate build_list_pat_def;
val r = translate list_cart_prod_def;
val r = translate cart_prod_def;
val r = translate build_binop_def;
val r = translate build_list_exp_def;
val r = translate build_funapp_def;
val r = translate build_fun_lam_def;
val r = translate build_letrec_binding_def;
val r = translate build_lets_def;
val r = translate build_pmatch_def;
val r = translate build_match_def;
val r = translate build_handle_def;
val r = translate build_function_def;
val r = translate bool_to_exp_def;
val r = translate flatten_pmatch_def;

val r = translate PART_DEF;
val r = translate PARTITION_DEF;

val r = m_translate path_to_ns_def;
val r = m_translate mapM_def;
val r = m_translate nterm_of_def;

val r = m_translate ptree_OperatorName_def;
val r = m_translate ptree_ModuleName_def;
val r = m_translate ptree_ModulePath_def;
val r = m_translate ptree_ValueName_def;
val r = m_translate ptree_ValuePath_def;
val r = m_translate ptree_TypeConstrName_def;
val r = m_translate ptree_TypeConstr_def;
val r = m_translate ptree_ConstrName_def;
val r = m_translate ptree_Constr_def;
val r = m_translate ptree_Ident_def;
val r = m_translate ptree_TVar_def;
val r = m_translate ptree_Type_def;
val r = m_translate ptree_Pattern_def;
val r = m_translate ptree_Patterns_def;
val r = m_translate ptree_Bool_def;

(* This takes a long time.
 *)

val r = m_translate ptree_Expr_def;

Theorem ptree_Expr_preconds[local]:
  (∀x y s. ptree_expr_side s x y) ∧
  (∀x s. ptree_letrecbinding_side s x) ∧
  (∀x s. ptree_letrecbindings_side s x) ∧
  (∀x s. ptree_letbinding_side s x) ∧
  (∀x s. ptree_letbindings_side s x) ∧
  (∀x s. ptree_patternmatches_side s x) ∧
  (∀x s. ptree_patternmatch_side s x) ∧
  (∀x s. ptree_exprlist_side s x) ∧
  (∀x s. ptree_exprcommas_side s x)
Proof
  ho_match_mp_tac ptree_Expr_ind
  \\ strip_tac
  >- simp [Once (fetch "-" "ptree_expr_side_def")]
  \\ strip_tac
  >- (
    reverse (Induct_on ‘nterm’) \\ gs []
    >- simp [Once (fetch "-" "ptree_expr_side_def")]
    \\ qx_gen_tac ‘et’ \\ qx_gen_tac ‘nterm’
    \\ Cases_on ‘nterm ≠ et’ \\ gs []
    >- (
      rpt strip_tac
      \\ simp [Once (fetch "-" "ptree_expr_side_def")])
    \\ simp [SF CONJ_ss]
    \\ rpt strip_tac
    \\ simp [Once (fetch "-" "ptree_expr_side_def")]
    \\ rw [] \\ gs [caml_lexTheory.isSymbol_thm])
  \\ rw []
  \\ simp [Once (fetch "-" "ptree_expr_side_def")]
QED

val _ = List.app (ignore o update_local_precondition)
                 (CONJUNCTS ptree_Expr_preconds);

val r = m_translate ptree_ConstrArgs_def;
val r = m_translate ptree_ConstrDecl_def;
val r = m_translate ptree_ExcDefinition_def;
val r = m_translate ptree_TypeRepr_def;
val r = m_translate ptree_TypeInfo_def;
val r = m_translate ptree_TypeName_def;
val r = m_translate ptree_TypeParamList_def;
val r = m_translate ptree_TypeParams_def;
val r = m_translate ptree_TypeDef_def;
val r = m_translate ptree_TypeDefs_def;

Theorem ISL_def:
  ISL x = case x of INL _ => T | _ => F
Proof
  CASE_TAC \\ rw [ISL]
QED

Theorem ISR_def:
  ISR x = case x of INR _ => T | _ => F
Proof
  CASE_TAC \\ rw [ISR]
QED

val r = translate ISL_def;
val r = translate ISR_def;
val r = translate OUTL;
val r = translate OUTR;
val r = m_translate ptree_TypeDefinition_def;

Theorem ptree_typedefinition_side[local]:
  ∀s x. ptree_typedefinition_side s x
Proof
  rw [fetch "-" "ptree_typedefinition_side_def",
      fetch "-" "outr_side_def", fetch "-" "outl_side_def"]
  \\ gs [EVERY_MEM, FORALL_PROD, quantHeuristicsTheory.ISR_exists,
         quantHeuristicsTheory.ISL_exists, SF SFY_ss]
  \\ res_tac \\ gs []
  \\ qpat_x_assum ‘PARTITION _ _ = _’ (assume_tac o SYM)
  \\ gs [PARTITION_DEF]
  \\ drule_then assume_tac PARTs_HAVE_PROP
  \\ gs [FORALL_PROD]
  \\ gs [EVERY_MEM, FORALL_PROD, quantHeuristicsTheory.ISR_exists,
         quantHeuristicsTheory.ISL_exists, SF SFY_ss]
  \\ strip_tac
  \\ res_tac
  \\ gvs []
QED

val _ = update_local_precondition ptree_typedefinition_side;

val r = translate build_dlet_def;

val r = m_translate ptree_Semis_def;
val r = m_translate ptree_ExprDec_def;
val r = m_translate ptree_Definition_def;
val r = m_translate ptree_Start_def;

val r = m_translate_run run_ptree_conv_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val () = ml_translatorLib.clean_on_exit := true;

val _ = export_theory ();

