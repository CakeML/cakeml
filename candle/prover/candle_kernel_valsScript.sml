(*
  Theorems about values from the Candle kernel program
 *)

open preamble;
open ml_translatorTheory ml_translatorLib ml_hol_kernelProgTheory;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     ast_extrasTheory finite_mapTheory pred_setTheory;
open basisFunctionsLib holKernelProofTheory;

val _ = new_theory "candle_kernel_vals";

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
  |> map (fn t => hd t |> snd |> fst)
  |> curry (op @) [constants_v_def]
  |> LIST_CONJ;

Definition kernel_locs_def:
  kernel_locs =
    { l | Loc l ∈ { the_type_constants
                  ; the_term_constants
                  ; the_axioms
                  ; the_context}}
End

fun get_constructors th =
  th |> concl |> find_terms (can $ match_term “TypeStamp _ _”)
     |> map (rand o rator)
     |> pred_setSyntax.mk_set;

Overload type_ctors_set[local] = (get_constructors TYPE_TYPE_def);
Overload term_ctors_set[local] = (get_constructors TERM_TYPE_def);
Overload thm_ctors_set[local] = (get_constructors THM_TYPE_def);

Definition kernel_ctors_def:
  kernel_ctors = type_ctors_set ∪
                 term_ctors_set ∪
                 thm_ctors_set
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
           s ∈ type_ctors_set
End

Definition TERM_TYPE_HEAD_def:
  TERM_TYPE_HEAD v ⇔
    ∃s vs. v = Conv (SOME (TypeStamp s term_stamp_n)) vs ∧
           s ∈ term_ctors_set
End

Definition THM_TYPE_HEAD_def:
  THM_TYPE_HEAD v ⇔
    ∃s vs. v = Conv (SOME (TypeStamp s thm_stamp_n)) vs ∧
           s ∈ thm_ctors_set
End

Theorem THM_TYPE_HEAD_def = SIMP_RULE list_ss [] THM_TYPE_HEAD_def;

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
  \\ once_rewrite_tac [kernel_funs_v_def]
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

(* -------------------------------------------------------------------------
 * Theorems applying kernel functions to *any* arguments (incl. wrong type)
 * ------------------------------------------------------------------------- *)

Theorem is_type_v_head:
  do_opapp [is_type_v; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    TYPE_TYPE_HEAD w
Proof
  Cases_on ‘TYPE_TYPE_HEAD w’
  \\ fs [is_type_v_def,do_opapp_def] \\ strip_tac \\ rpt var_eq_tac
  \\ pop_assum mp_tac
  \\ simp [evaluate_def,astTheory.pat_bindings_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ Cases_on ‘w’
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ gvs [AllCaseEqs()]
  \\ strip_tac \\ fs [] \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [same_type_def,same_ctor_def,LENGTH_EQ_NUM_compute]
  \\ gvs [do_app_def] \\ fs [TYPE_TYPE_HEAD_def]
QED

Theorem trans_v_head:
  do_partial_app trans_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧ THM_TYPE_HEAD w
Proof
  rewrite_tac [trans_v_def]
  \\ qmatch_goalsub_rename_tac ‘Mat _ [(_, Mat _ [(_, ee)])]’
  \\ strip_tac
  \\ gvs [trans_v_def,do_partial_app_def,do_opapp_def]
  \\ gvs [evaluate_def,AllCaseEqs()]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac
  \\ Cases_on ‘v’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ gvs [ml_progTheory.nsLookup_Short_def,pmatch_def,
          ml_progTheory.nsLookup_nsBind_compute]
  \\ Cases_on ‘v'’ \\ gvs [pmatch_def]
  \\ Cases_on ‘o'’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ fs [THM_TYPE_HEAD_def]
QED

Theorem Conv_NOT_IN_kernel_funs[simp]:
  ~(Conv opt vs ∈ kernel_funs)
Proof
  rewrite_tac [kernel_funs_def,IN_INSERT]
  \\ once_rewrite_tac [kernel_funs_v_def]
  \\ EVAL_TAC
QED

Theorem list_not_TERM_TYPE[simp]:
  ¬TERM_TYPE tm (Conv (SOME (TypeStamp nm list_type_num)) vs)
Proof
  Cases_on ‘tm’ \\ rw [TERM_TYPE_def] \\ gs [list_type_num_def]
QED

Theorem list_not_THM_TYPE[simp]:
  ¬THM_TYPE th (Conv (SOME (TypeStamp nm list_type_num)) vs)
Proof
  Cases_on ‘th’ \\ rw [THM_TYPE_def] \\ gs [list_type_num_def]
QED

Theorem list_type_NOTIN_kernel_types[simp]:
  list_type_num ∉ kernel_types
Proof
  rw [list_type_num_def, kernel_types_def]
QED

val _ = reset_translation();

val _ = export_theory ();
