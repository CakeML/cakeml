(*
 * Translates definitions to generate Dafny's AST from S-expressions.
 *)

open preamble ml_translatorLib
open dafny_sexpProgTheory
open sexp_to_dafnyTheory

val _ = new_theory "sexp_to_dafnyProg";

val _ = translation_extends "dafny_sexpProg";

val r = translate sexp_to_dafnyTheory.dstrip_sexp_def;
val r = translate sexp_to_dafnyTheory.strip_sxcons_def;
val r = translate sexp_to_dafnyTheory.sxstr_to_str_def;
val r = translate sexp_to_dafnyTheory.sxstr_to_ch_def;
val r = translate sexp_to_dafnyTheory.sxnum_to_num_def;
val r = translate sexp_to_dafnyTheory.sxsym_to_bool_def;

(* Expressions about EL were copied from to_flatProgScript.sml *)
val r = translate EL;
val el_side = Q.prove(
  `!n xs. el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "el_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [])
  |> update_precondition;
val r = translate optionTheory.OPTION_BIND_def;
val r = translate sexp_to_dafnyTheory.sxsym_to_opt_def;

val r = translate listTheory.OPT_MMAP_def;
val r = translate sexp_to_dafnyTheory.opt_mmap_sexp_list_def;

val r = translate optionTheory.OPTION_GUARD_def;
val r = translate optionTheory.OPTION_IGNORE_BIND_def;
val r = translate sexp_to_dafnyTheory.sexp_name_def;

val r = translate sexp_to_dafnyTheory.sexp_ident_def;
val r = translate sexp_to_dafnyTheory.sexp_attribute_def;
val r = translate sexp_to_dafnyTheory.sexp_primitive_def;
val r = translate sexp_to_dafnyTheory.sexp_collKind_def;
val r = translate sexp_to_dafnyTheory.sexp_typeArgBound_def;
val r = translate sexp_to_dafnyTheory.sexp_typeArgDecl_def;
val r = translate sexp_to_dafnyTheory.sexp_newtypeRange_def;
val r = translate sexp_to_dafnyTheory.sexp_unaryOp_def;
val r = translate sexp_to_dafnyTheory.sexp_binOp_def;
val r = translate sexp_to_dafnyTheory.sexp_datatypeType_def;

val r = sexp_to_dafnyTheory.sexp_type_def
          |> SRULE[oneline OPTION_BIND_def, UNCURRY]
          |> translate_no_ind;

(* Proof takes around one minute *)
Triviality sexp_type_ind:
  sexp_type_ind
Proof
  once_rewrite_tac [fetch "-" "sexp_type_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  >>~- ([`∀se rest. ses = se::rest ⇒ P se`],
        res_tac >> simp[])
  >>~- ([`FST foo = "ResolvedType.Newtype"`],
        (PairCases_on `foo`
         >> rpt (pop_assum mp_tac)
         >> once_rewrite_tac[FST, SND, EL]
         >> rpt strip_tac
         >> res_tac))
  \\ gvs [AllCaseEqs(), oneline dstrip_sexp_def]
QED

val _ = sexp_type_ind |> update_precondition;

val r = translate sexp_to_dafnyTheory.sexp_literal_def;
val r = translate sexp_to_dafnyTheory.sexp_formal_def;
val r = translate sexp_to_dafnyTheory.sexp_callSignature_def;
val r = translate sexp_to_dafnyTheory.sexp_callName_def;

Triviality OPTION_BIND_dstrip_sexp:
  OPTION_BIND (dstrip_sexp x) f =
  case dstrip_sexp x of
  | SOME (ss,as) => f (ss,as)
  | NONE => NONE
Proof
  Cases_on ‘dstrip_sexp x’ \\ gvs []
  \\ rename [‘_ = SOME x’] \\ PairCases_on ‘x’ \\ gvs []
QED

Triviality OPTION_BIND_strip_sxcons:
  OPTION_BIND (strip_sxcons x) f =
  case strip_sxcons x of
  | SOME l => f l
  | NONE => NONE
Proof
  Cases_on ‘strip_sxcons x’ \\ gvs []
QED

val r = sexp_to_dafnyTheory.sexp_statement_def
          |> SRULE [OPTION_BIND_dstrip_sexp]
          |> SRULE [oneline OPTION_BIND_def]
          |> SRULE [UNCURRY]
          |> REWRITE_RULE [GSYM EL]
          |> translate_no_ind;

Triviality pair_eq_lemma:
  x = y ⇔ FST x = FST y ∧ SND x = SND y
Proof
  PairCases_on ‘x’ \\ PairCases_on ‘y’ \\ gvs []
QED

Triviality sexp_assignlhs_ind: (* this is a slow proof, but it works *)
  sexp_assignlhs_ind
Proof
  once_rewrite_tac [fetch "-" "sexp_assignlhs_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ rpt strip_tac
  \\ rpt $ qpat_x_assum ‘∀x. _’ mp_tac
  \\ asm_rewrite_tac [PAIR_EQ,SOME_11,EL]
  \\ rpt $ disch_then (assume_tac o SRULE [])
  \\ metis_tac []
QED

val _ = sexp_assignlhs_ind |> update_precondition;

val side_lemma =
  sexp_assignlhs_ind |> REWRITE_RULE [fetch "-" "sexp_assignlhs_ind_def"]
  |> SPECL [“sexp_assignlhs_side”,
            “sexp_expression_side”,
            “map_sexp_expression_side”,
            “map_sexp_expression_sexp_expression_tuple_side”,
            “map_sxstr_to_str_sexp_expression_tuple_side”,
            “map_sexp_formal_sexp_expression_tuple_side”,
            “opt_sexp_expression_side”,
            “sexp_statement_side”,
            “map_sexp_statement_side”]

(*
Triviality sexp_assignlhs_side:
  ^(side_lemma |> concl |> dest_imp |> snd)
Proof
  match_mp_tac side_lemma
  \\ rpt strip_tac
  \\ once_rewrite_tac [fetch "-" "sexp_assignlhs_side_def"]
  \\ rpt strip_tac
  \\ ...
QED
*)

val r = translate sexp_to_dafnyTheory.sexp_method_def;
val r = translate sexp_to_dafnyTheory.sexp_field_def;
val r = translate sexp_to_dafnyTheory.sexp_classItem_def;
val r = translate sexp_to_dafnyTheory.sexp_class_def;
val r = translate sexp_to_dafnyTheory.sexp_trait_def;
val r = translate sexp_to_dafnyTheory.sexp_newtype_def;
val r = translate sexp_to_dafnyTheory.sexp_datatypeDtor_def;
val r = translate sexp_to_dafnyTheory.sexp_datatypeCtor_def;
val r = translate sexp_to_dafnyTheory.sexp_datatype_def;

Triviality bind_guard:
  OPTION_IGNORE_BIND (OPTION_GUARD b) x =
  if b then x else NONE
Proof
  Cases_on ‘b’ \\ gvs []
QED

val res = sexp_to_dafnyTheory.sexp_module_def
          |> SRULE [OPTION_BIND_dstrip_sexp]
          |> SRULE [oneline OPTION_BIND_def,bind_guard]
          |> SRULE [UNCURRY]
          |> REWRITE_RULE [GSYM EL]
          |> translate_no_ind;

Triviality sexp_module_ind:
  sexp_module_ind
Proof
  once_rewrite_tac [fetch "-" "sexp_module_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = sexp_module_ind |> update_precondition;

val r = translate sexp_to_dafnyTheory.sexp_program_def;

val _ = export_theory ();
