(*
  Theorems about values from the Candle kernel program
 *)

open preamble;
open ml_translatorTheory ml_hol_kernelProgTheory;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     namespacePropsTheory evaluatePropsTheory ast_extrasTheory
     holKernelProofTheory evaluateTheory permsTheory;

val _ = new_theory "candle_kernel_vals";

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
    call_tyvars_v;
    call_type_subst_v;

    constants_v;
    get_const_type_v;
    new_constant_v;
    call_type_of_v;
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
    call_frees_v;
    freesl_v;
    call_freesin_v;
    call_vfree_in_v;
    call_type_vars_in_term_v;
    call_variant_v;
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

Theorem IN_kernel_locs:
  n ∈ kernel_locs ⇔
  Loc n = the_type_constants ∨
  Loc n = the_term_constants ∨
  Loc n = the_axioms ∨
  Loc n = the_context
Proof
  fs [kernel_locs_def]
QED

Definition kernel_perms_def:
  kernel_perms = IMAGE RefMention kernel_locs
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

Definition LIST_TYPE_HEAD_def:
  LIST_TYPE_HEAD h v = ∃l:unit list. LIST_TYPE (K h) l v
End

Definition PAIR_TYPE_HEAD_def:
  PAIR_TYPE_HEAD h1 h2 v = PAIR_TYPE (K h1) (K h2) ((),()) v
End

(* -------------------------------------------------------------------------
 * THM, TERM, TYPE lemmas
 * ------------------------------------------------------------------------- *)

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

val s = “s:α semanticPrimitives$state”

val safe_error_goal =
    “∃k. s' = ((s:α semanticPrimitives$state) with clock := k) ∧
         (res = Rerr (Rabort Rtype_error) ∨
          res = Rerr (Rraise bind_exn_v) ∨
          res = Rerr (Rabort Rtimeout_error) :(v list, v) semanticPrimitives$result)”

Triviality same_clock_exists:
  (∃k. s = s with clock := k) = T ∧
  (∃k. s with clock := k' = s with clock := k) = T
Proof
  fs [state_component_equality]
QED

Theorem evaluate_ty_check:
  evaluate ^s env
    [Let NONE
       (Mat (Var (Short v))
          [(Pcon (SOME (Short "Tyvar")) [Pvar a1], Con NONE []);
           (Pcon (SOME (Short "Tyapp")) [Pvar a3; Pvar a4], Con NONE [])]) ee] = (s',res) ∧
  nsLookup env.c (Short "Tyvar") = SOME (1,TypeStamp "Tyvar" type_stamp_n) ∧
  nsLookup env.c (Short "Tyapp") = SOME (2,TypeStamp "Tyapp" type_stamp_n) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨ TYPE_TYPE_HEAD w ∧ evaluate ^s env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ fs [TYPE_TYPE_HEAD_def]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [namespaceTheory.nsOptBind_def]
QED

Theorem evaluate_tm_check:
  evaluate ^s env
    [Let NONE
       (Mat (Var (Short v))
          [(Pcon (SOME (Short "Var_1")) [Pvar a1; Pvar a2], Con NONE []);
           (Pcon (SOME (Short "Const")) [Pvar a3; Pvar a4], Con NONE []);
           (Pcon (SOME (Short "Comb")) [Pvar a5; Pvar a6], Con NONE []);
           (Pcon (SOME (Short "Abs")) [Pvar a7; Pvar a8], Con NONE [])]) ee] = (s',res) ∧
  nsLookup env.c (Short "Var_1") = SOME (2,TypeStamp "Var_1" term_stamp_n) ∧
  nsLookup env.c (Short "Const") = SOME (2,TypeStamp "Const" term_stamp_n) ∧
  nsLookup env.c (Short "Comb") = SOME (2,TypeStamp "Comb" term_stamp_n) ∧
  nsLookup env.c (Short "Abs") = SOME (2,TypeStamp "Abs" term_stamp_n) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨ TERM_TYPE_HEAD w ∧ evaluate ^s env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ fs [TERM_TYPE_HEAD_def]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [namespaceTheory.nsOptBind_def]
QED

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

Theorem concl_v_head:
  do_opapp [concl_v; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v
Proof
  rewrite_tac [concl_v_def]
  \\ qmatch_goalsub_rename_tac ‘Mat _ [(_, ee)]’
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
  \\ gvs [THM_TYPE_HEAD_def]
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

Theorem check_tm_head:
  ∀v s.
    ∃env e s' res.
      do_opapp [check_tm_v; v] = SOME (env,e) ∧
      evaluate (dec_clock ^s) env [e] = (s',res) ∧
      (^safe_error_goal ∨
       ∃k z. s' = s with clock := k ∧ res = Rval [z] ∧
       LIST_TYPE_HEAD TERM_TYPE_HEAD v)
Proof
  strip_tac \\ completeInduct_on ‘v_size v’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ rename [‘do_opapp [_; v]’]
  \\ simp [check_tm_v_def]
  \\ simp [do_opapp_def]
  \\ once_rewrite_tac [find_recfun_def] \\ fs []
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 fs [dec_clock_def,same_clock_exists]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [pmatch_def]
  \\ reverse CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ Cases_on ‘v’ \\ simp_tac (srw_ss()) [pmatch_def]
  \\ Cases_on ‘o'’ \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  THEN1
   (rpt var_eq_tac
    \\ simp_tac (srw_ss()) [evaluate_def]
    \\ rpt (CASE_TAC \\ gvs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS])
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ gvs []
    \\ fs [LIST_TYPE_HEAD_def]
    \\ qexists_tac ‘[]’
    \\ fs [LIST_TYPE_def])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1
   (simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
    \\ simp_tac (srw_ss()) [pmatch_def,dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ qmatch_goalsub_abbrev_tac ‘xx = (_,_)’
  \\ ‘∃res s. xx = (s,res)’ by metis_tac [PAIR]
  \\ fs [Abbr ‘xx’]
  \\ drule evaluate_tm_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ pop_assum mp_tac
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [build_rec_env_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [GSYM check_tm_v_def]
  \\ rename [‘do_opapp [_; h_tail]’]
  \\ last_x_assum (qspecl_then [‘h_tail’,‘dec_clock s’] mp_tac)
  \\ impl_tac THEN1 fs [v_size_def]
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS]
  \\ fs [LIST_TYPE_HEAD_def]
  \\ qexists_tac ‘()::l’
  \\ fs [LIST_TYPE_def,PAIR_TYPE_HEAD_def,PAIR_TYPE_def]
  \\ rpt (pop_assum mp_tac)
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
QED

Theorem check_ty_head:
  ∀v s.
    ∃env e s' res.
      do_opapp [check_ty_v; v] = SOME (env,e) ∧
      evaluate (dec_clock ^s) env [e] = (s',res) ∧
      (^safe_error_goal ∨
       ∃k z. s' = s with clock := k ∧ res = Rval [z] ∧
       LIST_TYPE_HEAD TYPE_TYPE_HEAD v)
Proof
  strip_tac \\ completeInduct_on ‘v_size v’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ rename [‘do_opapp [_; v]’]
  \\ simp [check_ty_v_def]
  \\ simp [do_opapp_def]
  \\ once_rewrite_tac [find_recfun_def] \\ fs []
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 fs [dec_clock_def,same_clock_exists]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [pmatch_def]
  \\ reverse CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ Cases_on ‘v’ \\ simp_tac (srw_ss()) [pmatch_def]
  \\ Cases_on ‘o'’ \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  THEN1
   (rpt var_eq_tac
    \\ simp_tac (srw_ss()) [evaluate_def]
    \\ rpt (CASE_TAC \\ gvs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS])
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ gvs []
    \\ fs [LIST_TYPE_HEAD_def]
    \\ qexists_tac ‘[]’
    \\ fs [LIST_TYPE_def])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1
   (simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
    \\ simp_tac (srw_ss()) [pmatch_def,dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ qmatch_goalsub_abbrev_tac ‘xx = (_,_)’
  \\ ‘∃res s. xx = (s,res)’ by metis_tac [PAIR]
  \\ fs [Abbr ‘xx’]
  \\ drule evaluate_ty_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ pop_assum mp_tac
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [build_rec_env_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [GSYM check_ty_v_def]
  \\ rename [‘do_opapp [_; h_tail]’]
  \\ last_x_assum (qspecl_then [‘h_tail’,‘dec_clock s’] mp_tac)
  \\ impl_tac THEN1 fs [v_size_def]
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS]
  \\ fs [LIST_TYPE_HEAD_def]
  \\ qexists_tac ‘()::l’
  \\ fs [LIST_TYPE_def,PAIR_TYPE_HEAD_def,PAIR_TYPE_def]
  \\ rpt (pop_assum mp_tac)
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
QED

Theorem check_tm_tm_head:
  ∀v s.
    ∃env e s' res.
      do_opapp [check_tm_tm_v; v] = SOME (env,e) ∧
      evaluate (dec_clock ^s) env [e] = (s',res) ∧
      (^safe_error_goal ∨
       ∃k z. s' = s with clock := k ∧ res = Rval [z] ∧
       LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v)
Proof
  strip_tac \\ completeInduct_on ‘v_size v’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ rename [‘do_opapp [_; v]’]
  \\ simp [check_tm_tm_v_def]
  \\ simp [do_opapp_def]
  \\ once_rewrite_tac [find_recfun_def] \\ fs []
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 fs [dec_clock_def,same_clock_exists]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [pmatch_def]
  \\ reverse CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ Cases_on ‘v’ \\ simp_tac (srw_ss()) [pmatch_def]
  \\ Cases_on ‘o'’ \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  THEN1
   (rpt var_eq_tac
    \\ simp_tac (srw_ss()) [evaluate_def]
    \\ rpt (CASE_TAC \\ gvs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS])
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ gvs []
    \\ fs [LIST_TYPE_HEAD_def]
    \\ qexists_tac ‘[]’
    \\ fs [LIST_TYPE_def])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1
   (simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
    \\ simp_tac (srw_ss()) [pmatch_def,dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ qmatch_goalsub_abbrev_tac ‘xx = (_,_)’
  \\ ‘∃res s. xx = (s,res)’ by metis_tac [PAIR]
  \\ fs [Abbr ‘xx’]
  \\ pop_assum mp_tac
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 (rw [] \\ fs [dec_clock_def,same_clock_exists])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (rw [] \\ fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1 (rw [Once evaluate_def] \\ fs [dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac
  \\ Cases_on ‘h’ \\ fs [pmatch_def]
  \\ Cases_on ‘o'’ \\ fs [pmatch_def]
  \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ strip_tac
  \\ drule evaluate_tm_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ drule evaluate_tm_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ pop_assum mp_tac
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [build_rec_env_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [GSYM check_tm_tm_v_def]
  \\ rename [‘do_opapp [_; h_tail]’]
  \\ last_x_assum (qspecl_then [‘h_tail’,‘dec_clock s’] mp_tac)
  \\ impl_tac THEN1 fs [v_size_def]
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS]
  \\ fs [LIST_TYPE_HEAD_def]
  \\ qexists_tac ‘()::l’
  \\ fs [LIST_TYPE_def,PAIR_TYPE_HEAD_def,PAIR_TYPE_def]
  \\ rpt (pop_assum mp_tac)
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
QED

Theorem check_ty_ty_head:
  ∀v s.
    ∃env e s' res.
      do_opapp [check_ty_ty_v; v] = SOME (env,e) ∧
      evaluate (dec_clock ^s) env [e] = (s',res) ∧
      (^safe_error_goal ∨
       ∃k z. s' = s with clock := k ∧ res = Rval [z] ∧
       LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v)
Proof
  strip_tac \\ completeInduct_on ‘v_size v’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ rename [‘do_opapp [_; v]’]
  \\ simp [check_ty_ty_v_def]
  \\ simp [do_opapp_def]
  \\ once_rewrite_tac [find_recfun_def] \\ fs []
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ rpt strip_tac
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 fs [dec_clock_def,same_clock_exists]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [pmatch_def]
  \\ reverse CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ Cases_on ‘v’ \\ simp_tac (srw_ss()) [pmatch_def]
  \\ Cases_on ‘o'’ \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  THEN1
   (rpt var_eq_tac
    \\ simp_tac (srw_ss()) [evaluate_def]
    \\ rpt (CASE_TAC \\ gvs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS])
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ gvs []
    \\ fs [LIST_TYPE_HEAD_def]
    \\ qexists_tac ‘[]’
    \\ fs [LIST_TYPE_def])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1
   (simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
    \\ simp_tac (srw_ss()) [pmatch_def,dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ qmatch_goalsub_abbrev_tac ‘xx = (_,_)’
  \\ ‘∃res s. xx = (s,res)’ by metis_tac [PAIR]
  \\ fs [Abbr ‘xx’]
  \\ pop_assum mp_tac
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 (rw [] \\ fs [dec_clock_def,same_clock_exists])
  \\ simp_tac (srw_ss()) [Once evaluate_def,ALL_DISTINCT,astTheory.pat_bindings_def]
  \\ CASE_TAC \\ fs []
  \\ TRY (rw [] \\ fs [dec_clock_def,same_clock_exists] \\ NO_TAC)
  THEN1 (rw [Once evaluate_def] \\ fs [dec_clock_def,same_clock_exists])
  \\ pop_assum mp_tac
  \\ Cases_on ‘h’ \\ fs [pmatch_def]
  \\ Cases_on ‘o'’ \\ fs [pmatch_def]
  \\ simp_tac (srw_ss()) [pmatch_def,AllCaseEqs(),same_ctor_def]
  \\ strip_tac \\ fs []
  \\ gvs [LENGTH_EQ_NUM_compute,pmatch_def]
  \\ strip_tac
  \\ drule evaluate_ty_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ drule evaluate_ty_check
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs [same_clock_exists]
  \\ pop_assum mp_tac
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [build_rec_env_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [GSYM check_ty_ty_v_def]
  \\ rename [‘do_opapp [_; h_tail]’]
  \\ last_x_assum (qspecl_then [‘h_tail’,‘dec_clock s’] mp_tac)
  \\ impl_tac THEN1 fs [v_size_def]
  \\ strip_tac \\ fs []
  \\ rw [] \\ fs [dec_clock_def,same_clock_exists,GSYM PULL_EXISTS]
  \\ fs [LIST_TYPE_HEAD_def]
  \\ qexists_tac ‘()::l’
  \\ fs [LIST_TYPE_def,PAIR_TYPE_HEAD_def,PAIR_TYPE_def]
  \\ rpt (pop_assum mp_tac)
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
QED

Theorem vsubst_v_head:
  do_partial_app vsubst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  rewrite_tac [vsubst_v_def]
  \\ qmatch_goalsub_rename_tac ‘Let NONE _ (Let NONE _ ee)’
  \\ strip_tac
  \\ gvs [do_partial_app_def,do_opapp_def]
  \\ pop_assum mp_tac
  \\ ntac 5 (simp [Once evaluate_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ qspecl_then [‘v’,‘s’] strip_assume_tac check_tm_tm_head
  \\ fs [] \\ rw [] \\ fs [namespaceTheory.nsOptBind_def] \\ rewrite_tac [same_clock_exists]
  \\ drule_then (qspec_then ‘w’ mp_tac) evaluate_tm_check
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ gvs [ml_progTheory.nsLookup_Short_def,pmatch_def,
          ml_progTheory.nsLookup_nsBind_compute,ml_progTheory.merge_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ fs [same_clock_exists]
QED

Theorem inst_v_head:
  do_partial_app inst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  rewrite_tac [inst_v_def]
  \\ qmatch_goalsub_rename_tac ‘Let NONE _ (Let NONE _ ee)’
  \\ strip_tac
  \\ gvs [do_partial_app_def,do_opapp_def]
  \\ pop_assum mp_tac
  \\ ntac 5 (simp [Once evaluate_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ qspecl_then [‘v’,‘s’] strip_assume_tac check_ty_ty_head
  \\ fs [] \\ rw [] \\ fs [namespaceTheory.nsOptBind_def] \\ rewrite_tac [same_clock_exists]
  \\ drule_then (qspec_then ‘w’ mp_tac) evaluate_tm_check
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ gvs [ml_progTheory.nsLookup_Short_def,pmatch_def,
          ml_progTheory.nsLookup_nsBind_compute,ml_progTheory.merge_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ fs [same_clock_exists]
QED

Theorem call_variant_v_head:
  do_partial_app call_variant_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD TERM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  rewrite_tac [call_variant_v_def]
  \\ qmatch_goalsub_rename_tac ‘Let NONE _ (Let NONE _ ee)’
  \\ strip_tac
  \\ gvs [do_partial_app_def,do_opapp_def]
  \\ pop_assum mp_tac
  \\ ntac 5 (simp [Once evaluate_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ qspecl_then [‘v’,‘s’] strip_assume_tac check_tm_head
  \\ fs [] \\ rw [] \\ fs [namespaceTheory.nsOptBind_def] \\ rewrite_tac [same_clock_exists]
  \\ drule_then (qspec_then ‘w’ mp_tac) evaluate_tm_check
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ gvs [ml_progTheory.nsLookup_Short_def,pmatch_def,
          ml_progTheory.nsLookup_nsBind_compute,ml_progTheory.merge_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ fs [same_clock_exists]
QED

Theorem beta_v_head:
  do_opapp [beta_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  rewrite_tac [beta_v_def]
  \\ qmatch_goalsub_rename_tac ‘Let NONE _ ee’
  \\ strip_tac
  \\ gvs [do_partial_app_def,do_opapp_def]
  \\ drule_then (qspec_then ‘v’ mp_tac) evaluate_tm_check
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ gvs [ml_progTheory.nsLookup_Short_def,pmatch_def,
          ml_progTheory.nsLookup_nsBind_compute,ml_progTheory.merge_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ fs [same_clock_exists]
QED

Theorem types_v_head:
  do_opapp [types_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    UNIT_TYPE () v
Proof
  rewrite_tac[types_v_def]
  \\ gvs[do_opapp_def]
  \\ strip_tac \\ rveq
  \\ fs[evaluate_def, astTheory.pat_bindings_def,
        pmatch_def, can_pmatch_all_def]
  \\ Cases_on`v` \\ fs[pmatch_def, same_clock_exists]
  \\ qmatch_asmsub_rename_tac`Conv co ca`
  \\ Cases_on`co` \\ fs[pmatch_def, same_clock_exists]
  \\ fs[CaseEqs ["list", "bool", "match_result", "option", "prod",
                 "v", "semanticPrimitives$result"],
        same_clock_exists, ml_translatorTheory.UNIT_TYPE_def]
QED

(* -------------------------------------------------------------------------
 * Misc. simps
 * ------------------------------------------------------------------------- *)

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

Theorem bool_type_NOTIN_kernel_types[simp]:
  bool_type_num ∉ kernel_types
Proof
  rw [bool_type_num_def, kernel_types_def]
QED

Theorem TYPE_TYPE_Vectorv[simp]:
  ¬TYPE_TYPE ty (Vectorv vs)
Proof
  Cases_on ‘ty’ \\ rw [TYPE_TYPE_def]
QED

Theorem TERM_TYPE_Vectorv[simp]:
  ¬TERM_TYPE tm (Vectorv vs)
Proof
  Cases_on ‘tm’ \\ rw [TERM_TYPE_def]
QED

Theorem THM_TYPE_Vectorv[simp]:
  ¬THM_TYPE th (Vectorv vs)
Proof
  Cases_on ‘th’ \\ rw [THM_TYPE_def]
QED

Theorem inferred_Vectorv[simp]:
  ¬inferred ctxt (Vectorv vs)
Proof
  rw [Once inferred_cases, kernel_funs_def]
  \\ once_rewrite_tac [kernel_funs_v_def] \\ gs []
QED

Theorem inferred_Conv:
  inferred ctxt (Conv (SOME stamp) vs) ⇒
    ∃tag m. stamp = TypeStamp tag m ∧ m ∈ kernel_types
Proof
  rw [Once inferred_cases, kernel_types_def]
  >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem inferred_Conv_NONE[simp]:
  ¬inferred ctxt (Conv NONE vs)
Proof
  rw [Once inferred_cases, kernel_types_def]
  >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem inferred_Loc[simp]:
  ¬inferred ctxt (Loc loc)
Proof
  rw [Once inferred_cases, kernel_funs_def]
  \\ once_rewrite_tac [kernel_funs_v_def] \\ gs []
  >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem inferred_Env[simp]:
  ¬inferred ctxt1 (Env env id)
Proof
  fs [inferred_cases]
  \\ conj_tac
  >- (EVAL_TAC \\ fs [] \\ rewrite_tac [kernel_funs_v_def] \\ EVAL_TAC)
  \\ rpt conj_tac \\ Cases
  \\ fs [TYPE_TYPE_def,TERM_TYPE_def,THM_TYPE_def]
QED

val _ = export_theory ();
