(*
  Theorems about values from the Candle kernel program
 *)

open preamble;
open ml_translatorTheory ml_hol_kernel_funsProgTheory candle_kernelProgTheory;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     namespacePropsTheory evaluatePropsTheory ast_extrasTheory
     holKernelProofTheory evaluateTheory permsTheory;

val _ = new_theory "candle_kernel_vals";

val _ = (max_print_depth := 10);

(* -------------------------------------------------------------------------
 * 'inferred' relation
 * ------------------------------------------------------------------------- *)

Definition kernel_funs_def:
  kernel_funs = {

  (* this list attempts to match the functions given in:
     https://github.com/jrh13/hol-light/blob/master/fusion.ml *)

    types_v;
    get_type_arity_v;
    call_new_type_v;
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
    abs_v;
    beta_v;
    assume_v;
    eq_mp_v;
    deduct_antisym_rule_v;
    inst_type_v;
    inst_1_v;
    axioms_v;
    new_axiom_v;
    new_basic_definition_v;
    new_basic_type_definition_v;
    new_specification_v;

    Kernel_print_thm_v;

    (* Compute additions *)
    compute_add_v;
    compute_v;
  }
End

Theorem kernel_funs_v_def =
  kernel_funs_def |> concl |> rand |> find_terms is_const
  |> filter (fn tm => not (mem (fst (dest_const tm)) ["INSERT","EMPTY"]))
  |> map (fn c => fst (dest_const c) ^ "_def")
  |> map (fn defn =>
      DB.find defn
      |> Lib.pluck (fn ((_,nm),_) => nm = defn)
      |> fst |> snd |> fst)
  |> curry (op @) [constants_v_def,abs_v_def]
  |> LIST_CONJ;

Theorem abs_v_def[compute] = abs_v_def;

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

val context_refs_defs = the_context_def |> concl |> find_terms (listSyntax.is_length)
  |> map (dest_thy_const o listSyntax.dest_length)
  |> map (fn cn => fetch (#Thy cn) (#Name cn ^ "_def"))

Theorem refs_defs = LIST_CONJ (cv_t_refs_def :: cv_f_refs_def :: context_refs_defs)

Theorem kernel_locs = IN_kernel_locs |>
  SIMP_RULE (srw_ss()) [the_type_constants_def,
                        the_term_constants_def,
                        the_axioms_def,
                        the_context_def,
                        refs_defs]

Definition kernel_perms_def:
  kernel_perms = IMAGE RefMention kernel_locs ∪ {RefUpdate}
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
  kernel_ffi = "kernel_ffi"
End

Definition thm2bytes_def:
  thm2bytes ctxt th =
    MAP (n2w:num->word8) (MAP ORD (explode (thm_to_string ctxt th)))
End

Definition ok_event_def:
  ok_event (IO_event n out y) ⇔
    n = kernel_ffi ⇒
      ∃ctxt th. THM ctxt th ∧
                thm2bytes ctxt th = out
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

Definition STRING_TYPE_HEAD_def:
  STRING_TYPE_HEAD v ⇔ ∃s. STRING_TYPE s v
End

Definition INT_HEAD_def:
  INT_HEAD v ⇔ ∃n. INT n v
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
          res = Rerr (Rabort Rtimeout_error)
            :(semanticPrimitives$v list, semanticPrimitives$v)
             semanticPrimitives$result)”

Theorem do_opapp_clos:
  do_opapp [Closure env v e; argv] = SOME (env1,e1) ⇔
  env with v := nsBind v argv env.v = env1 ∧ e = e1
Proof
  fs [do_opapp_def]
QED

Theorem do_partial_app_clos:
  do_partial_app (Closure env v (Fun n e)) argv = SOME g ⇔
  Closure (env with v := nsBind v argv env.v) n e = g
Proof
  fs [do_partial_app_def]
QED

Triviality same_clock_exists:
  (∃k. s = s with clock := k) = T ∧
  (∃k. s with clock := k' = s with clock := k) = T
Proof
  fs [state_component_equality]
QED

Theorem evaluate_unit_check:
  evaluate ^s (env with v := nsBind v w env1)
    [Mat (Var (Short v)) [(Pcon NONE [],ee)]] = (s',res) ⇒
  ^safe_error_goal ∨ UNIT_TYPE () w
Proof
  csimp [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def]
  \\ rw [AllCaseEqs(),same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
QED

Theorem evaluate_str_check:
  evaluate ^s env
    [Let NONE (App Strlen [Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨ STRING_TYPE_HEAD w ∧ evaluate ^s env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ last_x_assum (rewrite_tac o single o GSYM)
  \\ disj2_tac \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ fs [state_component_equality]
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
          [(Pcon (SOME (Short "Var"))   [Pvar a1; Pvar a2], Con NONE []);
           (Pcon (SOME (Short "Const")) [Pvar a3; Pvar a4], Con NONE []);
           (Pcon (SOME (Short "Comb"))  [Pvar a5; Pvar a6], Con NONE []);
           (Pcon (SOME (Short "Abs"))   [Pvar a7; Pvar a8], Con NONE [])]) ee] = (s',res) ∧
  nsLookup env.c (Short "Var")   = SOME (2,TypeStamp "Var" term_stamp_n) ∧
  nsLookup env.c (Short "Const") = SOME (2,TypeStamp "Const" term_stamp_n) ∧
  nsLookup env.c (Short "Comb")  = SOME (2,TypeStamp "Comb" term_stamp_n) ∧
  nsLookup env.c (Short "Abs")   = SOME (2,TypeStamp "Abs" term_stamp_n) ∧
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

Theorem evaluate_thm_check:
  evaluate ^s env
    [Let NONE
      (Mat (Var (Short v))
        [(Pcon (SOME (Short "Sequent")) [Pvar a1; Pvar a2], Con NONE [])]) ee] =
    (s',res) ∧
  nsLookup env.c (Short "Sequent") = SOME (2,TypeStamp "Sequent" thm_stamp_n) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨ THM_TYPE_HEAD w ∧ evaluate ^s env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ fs [THM_TYPE_HEAD_def]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [namespaceTheory.nsOptBind_def]
QED

Theorem evaluate_mat_pair:
  evaluate ^s env
    [Mat (Var (Short v)) [(Pcon NONE [Pvar a1; Pvar a2], ee)]] = (s',res) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  ∃v1 v2.
    w = Conv NONE [v1;v2] ∧
    evaluate s (env with v := nsBind a2 v2 (nsBind a1 v1 env.v)) [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,pmatch_def]
QED

Theorem evaluate_mat_thm:
  evaluate ^s env
    [Mat (Var (Short v))
       [(Pcon (SOME (Short "Sequent")) [Pvar a1; Pvar a2], ee)]] = (s',res) ∧
  nsLookup env.c (Short "Sequent") = SOME (2,TypeStamp "Sequent" thm_stamp_n) ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  ∃v1 v2.
    THM_TYPE_HEAD w ∧
    evaluate ^s (env with v := nsBind a2 v2 (nsBind a1 v1 env.v)) [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rpt strip_tac
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute,same_clock_exists]
  \\ Cases_on ‘w’ \\ gvs [pmatch_def]
  \\ rename [‘Conv oo ll’] \\ Cases_on ‘oo’ \\ gvs [pmatch_def,AllCaseEqs()]
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ rpt strip_tac \\ gvs [same_ctor_def,pmatch_def]
  \\ fs [THM_TYPE_HEAD_def]
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [namespaceTheory.nsOptBind_def] \\ rpt strip_tac \\ disj2_tac
  \\ first_x_assum $ irule_at Any
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

Theorem check_thm_head:
  ∀v s.
    ∃env e s' res.
      do_opapp [check_thm_v; v] = SOME (env,e) ∧
      evaluate (dec_clock ^s) env [e] = (s',res) ∧
      (^safe_error_goal ∨
       ∃k z. s' = s with clock := k ∧ res = Rval [z] ∧
       LIST_TYPE_HEAD THM_TYPE_HEAD v)
Proof
  strip_tac \\ completeInduct_on ‘v_size v’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ rename [‘do_opapp [_; v]’]
  \\ simp [check_thm_v_def]
  \\ simp [do_opapp_def]
  \\ once_rewrite_tac [find_recfun_def] \\ fs []
  \\ simp_tac (srw_ss()) [Once evaluate_def]
  \\ simp_tac (srw_ss()) [Once evaluate_def]
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
  \\ drule evaluate_thm_check
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
  \\ fs [GSYM check_thm_v_def]
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

Theorem evaluate_ty_list_check:
  evaluate ^s env
    [Let NONE (App Opapp [Var (Short "check_ty"); Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short "check_ty") = SOME check_ty_v ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  LIST_TYPE_HEAD TYPE_TYPE_HEAD w ∧
  ∃k. evaluate (^s with clock := k) env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ qspecl_then [‘w’,‘s’] mp_tac check_ty_head
  \\ fs [] \\ strip_tac \\ gvs [] \\ metis_tac []
QED

Theorem evaluate_thm_list_check:
  evaluate ^s env
    [Let NONE (App Opapp [Var (Short "check_thm"); Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short "check_thm") = SOME check_thm_v ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  LIST_TYPE_HEAD THM_TYPE_HEAD w ∧
  ∃k. evaluate (^s with clock := k) env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ qspecl_then [‘w’,‘s’] mp_tac check_thm_head
  \\ fs [] \\ strip_tac \\ gvs [] \\ metis_tac []
QED

Theorem evaluate_ty_ty_list_check:
  evaluate ^s env
    [Let NONE (App Opapp [Var (Short "check_ty_ty"); Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short "check_ty_ty") = SOME check_ty_ty_v ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) w ∧
  ∃k. evaluate (^s with clock := k) env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ qspecl_then [‘w’,‘s’] mp_tac check_ty_ty_head
  \\ fs [] \\ strip_tac \\ gvs [] \\ metis_tac []
QED

Theorem evaluate_tm_list_check:
  evaluate ^s env
    [Let NONE (App Opapp [Var (Short "check_tm"); Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short "check_tm") = SOME check_tm_v ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  LIST_TYPE_HEAD TERM_TYPE_HEAD w ∧
  ∃k. evaluate (^s with clock := k) env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ qspecl_then [‘w’,‘s’] mp_tac check_tm_head
  \\ fs [] \\ strip_tac \\ gvs [] \\ metis_tac []
QED

Theorem evaluate_tm_tm_list_check:
  evaluate ^s env
    [Let NONE (App Opapp [Var (Short "check_tm_tm"); Var (Short v)]) ee] = (s',res) ∧
  nsLookup env.v (Short "check_tm_tm") = SOME check_tm_tm_v ∧
  nsLookup env.v (Short v) = SOME w ⇒
  ^safe_error_goal ∨
  LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) w ∧
  ∃k. evaluate (^s with clock := k) env [ee] = (s',res)
Proof
  fs [evaluate_def,same_ctor_def,pmatch_def,do_con_check_def] \\ csimp []
  \\ fs [do_app_def,AllCaseEqs()] \\ strip_tac \\ gvs [same_clock_exists]
  \\ fs [STRING_TYPE_HEAD_def,STRING_TYPE_def,namespaceTheory.nsOptBind_def]
  \\ qspecl_then [‘w’,‘s’] mp_tac check_tm_tm_head
  \\ fs [] \\ strip_tac \\ gvs [] \\ metis_tac []
QED

Theorem types_v_head:
  do_opapp [types_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    UNIT_TYPE () v
Proof
  rewrite_tac[kernel_funs_v_def]
  \\ gvs[do_opapp_def]
  \\ strip_tac \\ rveq
  \\ drule evaluate_unit_check
  \\ rewrite_tac []
QED

Theorem constants_v_head:
  do_opapp [constants_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    UNIT_TYPE () v
Proof
  rewrite_tac[kernel_funs_v_def]
  \\ gvs[do_opapp_def]
  \\ strip_tac \\ rveq
  \\ drule evaluate_unit_check
  \\ rewrite_tac []
QED

Theorem axioms_v_head:
  do_opapp [axioms_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    UNIT_TYPE () v
Proof
  rewrite_tac[kernel_funs_v_def]
  \\ gvs[do_opapp_def]
  \\ strip_tac \\ rveq
  \\ drule evaluate_unit_check
  \\ rewrite_tac []
QED

Theorem mk_vartype_v_head:
  do_opapp [mk_vartype_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    ?x. STRING_TYPE x v
Proof
  rewrite_tac[mk_vartype_v_def]
  \\ gvs[do_opapp_def]
  \\ strip_tac \\ rveq
  \\ fs[evaluate_def, astTheory.pat_bindings_def,
        pmatch_def, can_pmatch_all_def, do_app_def]
  \\ fs[AllCaseEqs()] \\ gvs[same_clock_exists]
QED

Theorem call_new_type_v_head:
  do_opapp [call_new_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD STRING_TYPE_HEAD INT_HEAD v
Proof
  rewrite_tac[kernel_funs_v_def]
  \\ rewrite_tac [do_partial_app_clos,do_opapp_clos]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ rpt (
    (dxrule evaluate_str_check ORELSE dxrule evaluate_mat_pair)
    \\ simp [ml_progTheory.nsLookup_nsBind_compute]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ simp [same_clock_exists])
  \\ fs [PAIR_TYPE_HEAD_def,PAIR_TYPE_def]
  \\ pop_assum mp_tac
  \\ ntac 5 (simp [Once evaluate_def,do_app_def])
  \\ strip_tac \\ gvs [AllCaseEqs(),same_clock_exists]
  \\ fs [INT_HEAD_def,INT_def]
QED

val prove_head_tac =
  rewrite_tac[kernel_funs_v_def]
  \\ TRY (rename [‘Let (SOME xx) yy zz’])
  \\ rewrite_tac [do_partial_app_clos,do_opapp_clos]
  \\ strip_tac \\ rveq \\ rpt (pop_assum mp_tac)
  \\ rewrite_tac [do_partial_app_clos,do_opapp_clos]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ rpt (
    (dxrule evaluate_ty_check ORELSE
     dxrule evaluate_ty_list_check ORELSE
     dxrule evaluate_ty_ty_list_check ORELSE
     dxrule evaluate_tm_check ORELSE
     dxrule evaluate_tm_list_check ORELSE
     dxrule evaluate_tm_tm_list_check ORELSE
     dxrule evaluate_thm_check ORELSE
     dxrule evaluate_thm_list_check ORELSE
     dxrule evaluate_str_check ORELSE
     dxrule evaluate_mat_thm ORELSE
     dxrule evaluate_mat_pair)
    \\ simp [ml_progTheory.nsLookup_nsBind_compute,ml_progTheory.nsLookup_merge_env]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ rpt strip_tac \\ simp [same_clock_exists])
  \\ fs [PAIR_TYPE_HEAD_def,PAIR_TYPE_def];

Theorem is_type_v_head:
  do_opapp [is_type_v; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem concl_v_head:
  do_opapp [concl_v; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem trans_v_head:
  do_partial_app trans_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v ∧ THM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem beta_v_head:
  do_opapp [beta_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_variant_v_head:
  do_partial_app call_variant_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD TERM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem vsubst_v_head:
  do_partial_app vsubst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem dest_type_v_head:
  do_opapp [dest_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_type_v_head:
  do_opapp [is_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_vartype_v_head:
  do_opapp [is_vartype_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_var_v_head:
  do_opapp [is_var_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_const_v_head:
  do_opapp [is_const_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_abs_v_head:
  do_opapp [is_abs_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem is_comb_v_head:
  do_opapp [is_comb_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem rand_v_head:
  do_opapp [rand_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem rator_v_head:
  do_opapp [rator_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_var_v_head:
  do_opapp [dest_var_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_const_v_head:
  do_opapp [dest_const_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_comb_v_head:
  do_opapp [dest_comb_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_abs_v_head:
  do_opapp [dest_abs_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_vartype_v_head:
  do_opapp [dest_vartype_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_type_v_head:
  do_opapp [dest_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_eq_v_head:
  do_opapp [dest_eq_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_tyvars_v_head:
  do_opapp [call_tyvars_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_type_vars_in_term_v_head:
  do_opapp [call_type_vars_in_term_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_type_vars_in_term_v_head:
  do_opapp [call_type_vars_in_term_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem new_basic_definition_v_head:
  do_opapp [new_basic_definition_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem new_specification_v_head:
  do_opapp [new_specification_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem get_const_type_v_head:
  do_opapp [get_const_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    STRING_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem new_constant_v_head:
  do_opapp [new_constant_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem mk_var_v_head:
  do_opapp [mk_var_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem mk_comb_v_head:
  do_opapp [mk_comb_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem get_type_arity_v_head:
  do_opapp [get_type_arity_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    STRING_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem mk_type_v_head:
  do_opapp [mk_type_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD STRING_TYPE_HEAD (LIST_TYPE_HEAD TYPE_TYPE_HEAD) v
Proof
  prove_head_tac
QED

Theorem refl_v_head:
  do_opapp [refl_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem mk_const_v_head:
  do_opapp [mk_const_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD STRING_TYPE_HEAD
      (LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD)) v
Proof
  prove_head_tac
QED

Theorem freesl_v_head:
  do_opapp [freesl_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem assume_v_head:
  do_opapp [assume_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem hyp_v_head:
  do_opapp [hyp_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem dest_thm_v_head:
  do_opapp [dest_thm_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem mk_comb_1_v_head:
  do_opapp [mk_comb_1_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD THM_TYPE_HEAD THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem new_basic_type_definition_v_head:
  do_opapp [new_basic_type_definition_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    (PAIR_TYPE_HEAD STRING_TYPE_HEAD $
       PAIR_TYPE_HEAD STRING_TYPE_HEAD $
          PAIR_TYPE_HEAD STRING_TYPE_HEAD THM_TYPE_HEAD) v
Proof
  prove_head_tac
QED

Theorem call_type_subst_v_head:
  do_partial_app call_type_subst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v ∧
    TYPE_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem vsubst_v_head:
  do_partial_app vsubst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem inst_v_head:
  do_partial_app inst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem abs_v_head:
  do_partial_app abs_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD w ∧
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem eq_mp_v_head:
  do_partial_app eq_mp_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem deduct_antisym_rule_v_head:
  do_partial_app deduct_antisym_rule_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem inst_type_v_head:
  do_partial_app inst_type_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD w ∧
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v
Proof
  prove_head_tac
QED

Theorem inst_1_v_head:
  do_partial_app inst_1_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD w ∧
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v
Proof
  prove_head_tac
QED

Theorem new_axiom_v_head:
  do_opapp [new_axiom_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_type_of_v_head:
  do_opapp [call_type_of_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_vfree_in_v_head:
  do_partial_app call_vfree_in_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem call_freesin_v_head:
  do_partial_app call_freesin_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD TERM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem mk_abs_v_head:
  do_opapp [mk_abs_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem call_frees_v_head:
  do_opapp [call_frees_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    TERM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem inst_v_head:
  do_partial_app inst_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem Kernel_print_thm_v_head:
  do_opapp [Kernel_print_thm_v; v] = SOME (env, exp) ∧
  evaluate ^s env [exp] = (s', res) ⇒
    ^safe_error_goal ∨
    THM_TYPE_HEAD v
Proof
  prove_head_tac
QED

Theorem compute_add_v_head:
  do_partial_app compute_add_v v = SOME g ∧
  do_opapp [g; w] = SOME (env,exp) ∧
  evaluate ^s env [exp] = (s',res) ⇒
    ^safe_error_goal ∨
    LIST_TYPE_HEAD THM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
QED

Theorem compute_v_head:
  do_partial_app compute_v v = SOME g ∧
  do_opapp [g; w] = SOME (env,exp) ∧
  evaluate ^s env [exp] = (s',res) ⇒
    ^safe_error_goal ∨
    PAIR_TYPE_HEAD (LIST_TYPE_HEAD THM_TYPE_HEAD)
                   (LIST_TYPE_HEAD THM_TYPE_HEAD) v ∧
    TERM_TYPE_HEAD w
Proof
  prove_head_tac
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
