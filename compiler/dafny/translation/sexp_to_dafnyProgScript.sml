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

(* Expressions regarding EL were copied from to_flatProgScript.sml *)
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

val r = translate optionTheory.OPTION_IGNORE_BIND_def;
val r = translate optionTheory.OPTION_GUARD_def;
val r = translate sexp_to_dafnyTheory.opt_mmap_sexp_tuple_def;

val r = translate sexp_to_dafnyTheory.opt_mmap_sexp_tuple_list_def;
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

(* TODO just imitated sexp_type after sexp_statement didn't translate;
   not sure whether that makes sense *)
val r = translate_no_ind sexp_to_dafnyTheory.sexp_statement_def;
Triviality sexp_statement_ind:
  sexp_statement_ind
Proof
  (* once_rewrite_tac [fetch "-" "sexp_statement_ind_def"] *)
  (* \\ rpt gen_tac *)
  (* \\ rpt (disch_then strip_assume_tac) *)
  (* \\ match_mp_tac (latest_ind ()) *)
  (* \\ rpt strip_tac *)
  (* \\ last_x_assum match_mp_tac *)
  (* \\ rpt strip_tac *)
  (* \\ gvs [FORALL_PROD] *)
  cheat
QED
(* TODO does not seem to terminate *)
(* val _ = sexp_statement_ind |> update_precondition; *)

val r = translate sexp_to_dafnyTheory.sexp_method_def;
val r = translate sexp_to_dafnyTheory.sexp_field_def;
val r = translate sexp_to_dafnyTheory.sexp_classItem_def;
val r = translate sexp_to_dafnyTheory.sexp_class_def;
val r = translate sexp_to_dafnyTheory.sexp_trait_def;
val r = translate sexp_to_dafnyTheory.sexp_newtype_def;
val r = translate sexp_to_dafnyTheory.sexp_datatypeDtor_def;
val r = translate sexp_to_dafnyTheory.sexp_datatypeCtor_def;
val r = translate sexp_to_dafnyTheory.sexp_datatype_def;

(* Suggested by translator *)
val res = translate_no_ind sexp_to_dafnyTheory.sexp_module_def;
Triviality sexp_module_ind:
  sexp_module_ind
Proof
  (* once_rewrite_tac [fetch "-" "sexp_module_ind_def"] *)
  (* \\ rpt gen_tac *)
  (* \\ rpt (disch_then strip_assume_tac) *)
  (* \\ match_mp_tac (latest_ind ()) *)
  (* \\ rpt strip_tac *)
  (* \\ last_x_assum match_mp_tac *)
  (* \\ rpt strip_tac *)
  (* \\ gvs [FORALL_PROD] *)
  cheat
QED
val _ = sexp_module_ind |> update_precondition;

val r = translate sexp_to_dafnyTheory.sexp_program_def;

val _ = export_theory ();
