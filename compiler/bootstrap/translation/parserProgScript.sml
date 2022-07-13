(*
  Translate the compiler's parser.
*)
open preamble
     cmlParseTheory cmlPEGTheory lexerProgTheory
     ml_translatorLib ml_translatorTheory
     semanticPrimitivesTheory

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "parserProg"

val _ = translation_extends "lexerProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "parserProg");
val _ = ml_translatorLib.use_string_type true;

(* translator setup *)

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
val _ = add_preferred_thy "termination";

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

(* parsing: peg_exec and cmlPEG *)

val res = register_type``:(tokens$token,MMLnonT,locs) parsetree``;
val res = register_type``:MMLnonT``;

(* checking GRAMMAR_PARSETREE_TYPE etc is known to be an EqualityType *)
val EqType_PT_rule = EqualityType_rule [] ``:(tokens$token,MMLnonT,locs) parsetree``;

val _ = translate (def_of_const ``validAddSym``);

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

val _ = translate locnle;

Triviality validaddsym_side_lemma:
  ∀x. validaddsym_side x = T
Proof
  simp[fetch "-" "validaddsym_side_def"]
QED
val _ = update_precondition validaddsym_side_lemma;

val _ = translate (def_of_const ``cmlPEG``);

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

val _ = translate (def_of_const ``coreloop`` |> RW [INTRO_FLOOKUP]
                   |> SPEC_ALL |> RW1 [FUN_EQ_THM]);

val _ = translate (def_of_const ``peg_exec``);

(* parsing: cmlvalid *)

Theorem monad_unitbind_assert:
  !b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE
Proof
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []
QED

val _ = translate grammarTheory.ptree_head_def

(* parsing: ptree converstion *)

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

Theorem maybe_handleRef_eq:
  !p. maybe_handleRef p =
      case p of
      | (Pcon (SOME (Short n)) [pat]) => if n = "Ref" then Pref pat else p
      | _ => p
Proof
  recInduct cmlPtreeConversionTheory.maybe_handleRef_ind
  \\ rw [cmlPtreeConversionTheory.maybe_handleRef_def]
  \\ every_case_tac \\ fs []
QED

val _ = translate maybe_handleRef_eq

val _ = translate (def_of_const ``ptree_Expr``);

val _ = translate (def_of_const ``ptree_linfix``);

val _ = translate (def_of_const ``ptree_TypeDec``);

val _ = def_of_const “ptree_DtypeDecl” |> translate;

val def = cmlPtreeConversionTheory.ptree_SpeclineList_def
  |> SIMP_RULE (srw_ss()) [OPTION_CHOICE_def |> DefnBase.one_line_ify NONE,
                           OPTION_BIND_def |> DefnBase.one_line_ify NONE,
                           OPTION_IGNORE_BIND_def |> DefnBase.one_line_ify NONE,
                           OPTION_GUARD_def |> DefnBase.one_line_ify NONE]

val res = translate def;

val _ = def_of_const “ptree_SignatureValue” |> translate

Triviality ptree_Decls:
  ptree_Decls x =
     case x of
     | Lf t => ptree_Decls (Lf t)
     | Nd (a1,a2) b => ptree_Decls (Nd (a1,a2) b)
Proof
  Cases_on ‘x’ \\ fs []
  \\ rename [‘Nd p’] \\ PairCases_on ‘p’ \\ fs []
QED

Triviality ptree_Structure:
  ptree_Structure x =
     case x of
     | Lf t => ptree_Structure (Lf t)
     | Nd (a1,a2) b => ptree_Structure (Nd (a1,a2) b)
Proof
  Cases_on ‘x’ \\ fs []
  \\ rename [‘Nd p’] \\ PairCases_on ‘p’ \\ fs []
QED

val def =
  LIST_CONJ
    [cmlPtreeConversionTheory.ptree_Decl_def |> CONJUNCT1 |> SPEC_ALL,
     ptree_Decls
     |> ONCE_REWRITE_RULE  [cmlPtreeConversionTheory.ptree_Decl_def],
     ptree_Structure
     |> ONCE_REWRITE_RULE  [cmlPtreeConversionTheory.ptree_Decl_def]]
  |> SIMP_RULE (srw_ss()) [OPTION_CHOICE_def |> DefnBase.one_line_ify NONE,
                           OPTION_BIND_def |> DefnBase.one_line_ify NONE,
                           OPTION_IGNORE_BIND_def |> DefnBase.one_line_ify NONE,
                           OPTION_GUARD_def |> DefnBase.one_line_ify NONE]

val res = translate_no_ind def;

Triviality ind_lemma:
  ^(first is_forall (hyp res))
Proof
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac
      (cmlPtreeConversionTheory.ptree_Decl_ind
       |> SIMP_RULE (srw_ss()) [AllCaseEqs(),PULL_EXISTS])
  \\ rpt conj_tac
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ fs []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs()]
QED

val _ = ind_lemma |> update_precondition;

val _ = translate (def_of_const ``ptree_TopLevelDecs``);

(* parsing: top-level parser *)

val _ = translate (RW [monad_unitbind_assert] parse_prog_def);

Theorem parse_prog_side_lemma = Q.prove(`
  !x. parse_prog_side x = T`,
  SIMP_TAC std_ss [fetch "-" "parse_prog_side_def",
    fetch "-" "peg_exec_side_def", fetch "-" "coreloop_side_def"]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `v1` owhile_TopLevelDecs_total)
  THEN FULL_SIMP_TAC std_ss [INTRO_FLOOKUP] THEN POP_ASSUM MP_TAC
  THEN CONV_TAC (DEPTH_CONV ETA_CONV) THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
