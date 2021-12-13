(*
  Theorems about values from the Candle kernel program
 *)

open preamble;
open ml_translatorTheory ml_translatorLib ml_hol_kernelProgTheory;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     ast_extrasTheory finite_mapTheory pred_setTheory;
open basisFunctionsLib holKernelProofTheory;

val _ = new_theory "ml_hol_kernel_vals";

val _ = translation_extends "ml_hol_kernelProg";

(*
TODO:
 - fix constructor names (Var is currently Var_1)
 - add FFI call to kernel
 - ensure all kernel functions take at most two curried arguments
   (e.g. tweak new_basic_type_definition)
 - make sure (using local) that only intended values escape Candle kernel
 - tidy up the reference numbers, i.e. Loc values
*)


(* -------------------------------------------------------------------------
 * 'inferred' relation
 * ------------------------------------------------------------------------- *)

Definition kernel_funs_def:
  kernel_funs = {

  (* this list attempts to match the functions given in:
     https://github.com/jrh13/hol-light/blob/master/fusion.ml *)

    types_v;
    get_type_arity_v;
    new_type_v;
    mk_type_v;
    mk_vartype_v;
    dest_type_v;
    dest_vartype_v;
    is_type_v;
    is_vartype_v;
    tyvars_v;
    type_subst_v;

    constants_v;
    get_const_type_v;
    new_constant_v;
    type_of_v;
 (* alphaorder_v_def *)
    is_var_v;
    is_const_v;
    is_abs_v;
    is_comb_v;
    mk_var_v;
    mk_const_v;
    mk_abs_v;
    mk_comb_v;
    dest_var_v;
    dest_const_v;
    dest_comb_v;
    dest_abs_v;
    frees_v;
    freesl_v;
    freesin_v;
    vfree_in_v;
    type_vars_in_term_v;
    variant_v;
    vsubst_v;
    inst_v;
    rand_v;
    rator_v;
    dest_eq_v;

    dest_thm_v;
    hyp_v;
    concl_v;
    refl_v;
    trans_v;
    mk_comb_1_v;
    abs_1_v;
    beta_v;
    assume_v;
    eq_mp_v;
    deduct_antisym_rule_v;
    inst_type_v;
    inst_1_v;
    axioms_v;
    new_axiom_v;
 (* definitions_v_def *)
    new_basic_definition_v;
    new_basic_type_definition_v;

  }
End

Theorem kernel_funs_v_def =
  kernel_funs_def |> concl |> rand |> find_terms is_const
  |> filter (fn tm => not (mem (fst (dest_const tm)) ["INSERT","EMPTY"]))
  |> map (fn c => DB.find (fst (dest_const c) ^ "_def"))
  |> map (fn t => hd t |> snd |> fst) |> LIST_CONJ;

Definition kernel_locs_def:
  kernel_locs =
    { l | Loc l ∈ { the_type_constants
                  ; the_term_constants
                  ; the_axioms
                  ; the_context}}
End

fun get_typestamp_num th =
  th |> concl |> find_term (can $ match_term “TypeStamp _ _”) |> rand;

Overload type_stamp_n = (get_typestamp_num TYPE_TYPE_def);
Overload term_stamp_n = (get_typestamp_num TERM_TYPE_def);
Overload thm_stamp_n  = (get_typestamp_num THM_TYPE_def);

Definition kernel_types_def:
  kernel_types = { type_stamp_n; term_stamp_n; thm_stamp_n } : num set
End

Inductive inferred:
[~KernelFuns:]
  (∀ctxt f.
     f ∈ kernel_funs ⇒
       inferred ctxt f) ∧
[~TYPE:]
  (∀ctxt ty v.
     TYPE ctxt ty ∧
     TYPE_TYPE ty v ⇒
       inferred ctxt v) ∧
[~TERM:]
  (∀ctxt tm v.
     TERM ctxt tm ∧
     TERM_TYPE tm v ⇒
       inferred ctxt v) ∧
[~THM:]
  (∀ctxt th v.
     THM ctxt th ∧
     THM_TYPE th v ⇒
       inferred ctxt v)
End

Definition kernel_ffi_def:
  kernel_ffi = "kernel"
End

Definition thm2bytes_def:
  thm2bytes th = []:word8 list  (* TODO: fix me *)
End

Definition ok_event_def:
  ok_event ctxt (IO_event n out y) ⇔
    n = kernel_ffi ⇒
      ∃th v. THM ctxt th ∧
             THM_TYPE th v ∧
             thm2bytes th = out
End

(* -------------------------------------------------------------------------
 * Versions of TERM, THM that only match the outermost structure
 * ------------------------------------------------------------------------- *)

Definition TYPE_TYPE_HEAD_def:
  TYPE_TYPE_HEAD v ⇔
    ∃s vs. v = Conv (SOME (TypeStamp s type_stamp_n)) vs ∧
           s ∈ {"Tyapp"; "Tyvar"}
End

Definition TERM_TYPE_HEAD_def:
  TERM_TYPE_HEAD v ⇔
    ∃s vs. v = Conv (SOME (TypeStamp s term_stamp_n)) vs ∧
           s ∈ {"Abs"; "Comb"; "Const"; "Var_1"}
End

Definition THM_TYPE_HEAD_def:
  THM_TYPE_HEAD v ⇔
    ∃vs. v = Conv (SOME (TypeStamp "Thm" thm_stamp_n)) vs
End

(* -------------------------------------------------------------------------
 * THM, TERM, TYPE lemmas
 * ------------------------------------------------------------------------- *)

Theorem EqualityType_TYPE_TYPE = EqualityType_rule [] “:type”;

Theorem EqualityType_LIST_TYPE_TYPE_TYPE = EqualityType_rule [] “:type list”;

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_LIST_TYPE_TERM_TYPE = EqualityType_rule [] “:term list”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_LIST_TYPE_THM_TYPE = EqualityType_rule [] “:thm list”;

Theorem kernel_funs_inferred[simp]:
  (∀ty. v ∈ kernel_funs ⇒ ¬TYPE_TYPE ty v) ∧
  (∀tm. v ∈ kernel_funs ⇒ ¬TERM_TYPE tm v) ∧
  (∀th. v ∈ kernel_funs ⇒ ¬THM_TYPE th v)
Proof
  rpt conj_tac \\ Cases
  \\ fs [TYPE_TYPE_def, TERM_TYPE_def, THM_TYPE_def]
  \\ rw [] \\ qsuff_tac ‘F’ \\ fs []
  \\ pop_assum mp_tac \\ fs []
  \\ rewrite_tac [kernel_funs_def,IN_INSERT,NOT_IN_EMPTY]
  \\ once_rewrite_tac [kernel_funs_v_def,constants_v_def]
  \\ EVAL_TAC
QED

Theorem TYPE_from_TYPE_TYPE:
  inferred ctxt v ∧
  TYPE_TYPE ty v ⇒
    TYPE ctxt ty
Proof
  rw [Once inferred_cases] \\ gs []
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def]
    \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def]
    \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ assume_tac EqualityType_TYPE_TYPE
  \\ gs [EqualityType_def]
  \\ qpat_x_assum ‘∀a b c d. _ ⇒ (_ ⇔ _)’ (dxrule_then drule) \\ gs []
QED

Theorem TERM_from_TERM_TYPE:
  inferred ctxt v ∧
  TERM_TYPE tm v ⇒
    TERM ctxt tm
Proof
  rw [Once inferred_cases] \\ gs []
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def]
    \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  >~ [‘TYPE ctxt ty’] >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def]
    \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ assume_tac EqualityType_TERM_TYPE
  \\ gs [EqualityType_def]
  \\ qpat_x_assum ‘∀a b c d. _ ⇒ (_ ⇔ _)’ (dxrule_then drule) \\ gs []
QED

Theorem THM_from_THM_TYPE:
  inferred ctxt v ∧
  THM_TYPE th v ⇒
    THM ctxt th
Proof
  rw [Once inferred_cases] \\ gs []
  >~ [‘TYPE ctxt ty’] >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def]
    \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def]
    \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
  \\ assume_tac EqualityType_THM_TYPE
  \\ gs [EqualityType_def]
  \\ qpat_x_assum ‘∀a b c d. _ ⇒ (_ ⇔ _)’ (dxrule_then drule) \\ gs []
QED

(*

(* -------------------------------------------------------------------------
 * Theorems about partial application of values in kernel_funs.
 *
 * Hopefully we can stuff some forcing code (i.e. Seq) into the kernel
 * functions to make these theorems easier to prove.
 * ------------------------------------------------------------------------- *)

Theorem conj_v_alt:
  do_partial_app conj_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  simp [conj_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ Cases_on ‘w’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
QED

Theorem disj1_v_alt:
  do_partial_app disj1_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  simp [disj1_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ simp [do_con_check_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs []
  \\ cheat (* disj1 does not examine the constructor of its second argument *)
QED

Theorem imp_v_alt:
  do_partial_app imp_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  simp [imp_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ Cases_on ‘w’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
QED

Theorem not_not_v_alt:
  do_opapp [not_not_v; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v
Proof
  simp [not_not_v_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
QED

*)

val _ = reset_translation();

val _ = export_theory ();
