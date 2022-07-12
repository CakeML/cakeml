(*
  Real-number identity proofs for Icing optimisations supported by CakeML
  Each optimisation is defined in icing_optimisationsScript.
  This file proves that optimisations  are real-valued identities.
  The overall real-number simluation proof for a particular run of the optimiser
  from source_to_source2Script is build using the automation in
  icing_optimisationsLib and the general theorems from
  source_to_source2ProofsScript.
*)
open bossLib ml_translatorLib;
open semanticPrimitivesTheory evaluatePropsTheory;
open fpValTreeTheory fpSemPropsTheory fpOptTheory fpOptPropsTheory
     icing_optimisationsTheory icing_rewriterTheory source_to_source2ProofsTheory
     floatToRealTheory floatToRealProofsTheory icing_optimisationProofsTheory
     evaluateTheory pureExpsTheory binary_ieeeTheory realLib realTheory RealArith;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

open preamble;

val _ = new_theory "icing_realIdProofs";

val state_eqs = [state_component_equality, fpState_component_equality];

(** Automatically prove trivial goals about fp oracle **)
val fp_inv_tac = imp_res_tac evaluate_fp_opts_inv \\ fs[];

(** real number equivalences **)

Theorem isPureExp_realify:
  (∀e.
    isPureExp e ⇒
    isPureExp (realify e)) ∧
  (∀es.
    isPureExpList es ⇒
    isPureExpList (MAP realify es)) ∧
  (∀pes.
    isPurePatExpList pes ⇒
    isPurePatExpList (MAP (λ(p,e). (p,realify e)) pes))
Proof
  ho_match_mp_tac isPureExp_ind>>
  rw[isPureExp_def, floatToRealTheory.realify_def]>>fs[]
  >-
    (Cases_on`e`>>simp[isPureExp_def, floatToRealTheory.realify_def])
  >- (
    `(λa. realify a) = realify` by
        fs[ETA_AX]>>
    simp[])>>
  TOP_CASE_TAC>>
  `(λa. realify a) = realify` by fs[ETA_AX]>>
  fs[isPureExp_def,isPureOp_def]>>
  every_case_tac>>fs[isPureOp_def,isPureExp_def]>>
  simp[isPureOp_def]
QED

(* Not the full definition, since we only use together with isPureExp *)
Definition isIceFree_def:
  (isIceFree (App op exl) <=>
    (getOpClass op ≠ Icing ∨
    ?t. op = FP_top t ∧ LENGTH exl ≠ 3) ∧ isIceFreeList exl) /\
  (isIceFree (Tannot e a) = isIceFree e) /\
  (isIceFree (Lannot e l) = isIceFree e) /\
  (isIceFree (FpOptimise _ e) = isIceFree e) ∧
  (isIceFree (Con _ exl) <=> isIceFreeList exl) ∧
  (isIceFree (Log _ e1 e2) = (isIceFree e1 /\ isIceFree e2)) ∧
  (isIceFree (If e1 e2 e3) = (isIceFree e1 /\ isIceFree e2 /\ isIceFree e3)) /\
  (isIceFree (Mat e pel) = (isIceFree e /\ isIceFreePatExpList pel))  ∧
  (isIceFree (Let _ e1 e2) = (isIceFree e1 /\ isIceFree e2)) /\
  (isIceFree _ = T) /\
  (isIceFreeList [] = T) /\
  (isIceFreeList (e::exl) = (isIceFree e /\ isIceFreeList exl)) ∧
  (isIceFreePatExpList [] = T) /\
  (isIceFreePatExpList ((p,e)::pel) = (isIceFree e /\ isIceFreePatExpList pel))
Termination
  wf_rel_tac (`measure
    \ x. case x of
          | INL e => exp_size e
          | INR (INL exl) => exp6_size exl
          | INR (INR pel) => exp3_size pel`)
End

Theorem isIceFreeList_APPEND:
  ∀xs ys.
  isIceFreeList (xs ++ ys) ⇔
  isIceFreeList xs ∧ isIceFreeList ys
Proof
  Induct>>rw[isIceFree_def]>>
  metis_tac[]
QED

Theorem isIceFreeList_REVERSE:
  ∀es.
  isIceFreeList (REVERSE es) ⇔
  isIceFreeList es
Proof
  Induct>>fs[isIceFree_def,isIceFreeList_APPEND]>>
  metis_tac[]
QED

Theorem isIceFreeList_EVERY:
  ∀es.
  isIceFreeList es ⇔
  EVERY isIceFree es
Proof
  Induct>>fs[isIceFree_def]
QED

Theorem isIceFreePatExpList_EVERY:
  ∀pes.
  isIceFreePatExpList pes ⇔
  EVERY (λ(p,e). isIceFree e) pes
Proof
  Induct>>fs[isIceFree_def, FORALL_PROD]
QED

Theorem realify_IceFree:
  ∀e. isIceFree (realify e)
Proof
  ho_match_mp_tac floatToRealTheory.realify_ind>>
  rw[isIceFree_def,floatToRealTheory.realify_def]
  >-
    fs[isIceFreeList_EVERY,EVERY_MEM,MEM_MAP,PULL_EXISTS]
  >- (
    TOP_CASE_TAC>>
    simp[isIceFree_def,isIceFreeList_EVERY,EVERY_MEM,astTheory.getOpClass_def,MEM_MAP,PULL_EXISTS]>>
    every_case_tac>>
    simp[isIceFree_def,isIceFreeList_EVERY,EVERY_MEM,astTheory.getOpClass_def,MEM_MAP,PULL_EXISTS])>>
  simp[isIceFreePatExpList_EVERY,EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
  metis_tac[]
QED

Theorem evaluate_IceFree:
  (! (s1:'a semanticPrimitives$state) env e s2 r ee.
    evaluate s1 env e = (s2, Rval r) ∧
    isPureExpList e ∧
    isIceFreeList e
    ==>
    Abbrev (s1.fp_state.opts = s2.fp_state.opts ∧
    s1.fp_state.choices = s2.fp_state.choices)) ∧
  (! (s1:'a semanticPrimitives$state) env v pes errv s2 r pese.
    evaluate_match s1 env v pes errv = (s2, Rval r) ∧
    isPurePatExpList pes ∧
    isIceFreePatExpList pes
    ==>
    Abbrev (s1.fp_state.opts = s2.fp_state.opts ∧
    s1.fp_state.choices = s2.fp_state.choices))
Proof
  ho_match_mp_tac evaluate_ind>>
  rw[evaluate_def,isPureExp_def,isIceFree_def,isIceFreeList_REVERSE]>>rfs[markerTheory.Abbrev_def]
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (
    qpat_x_assum` _ = (_,_)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    TOP_CASE_TAC>>fs[]
    >- (
      fs[]>>
      every_case_tac>>fs[]>>
      fs[isPureOp_def])
    >- (
      fs[]>>
      every_case_tac>>fs[]>>
      fs[isPureOp_def])
    >> every_case_tac
    >>gs[state_component_equality,fpState_component_equality, isPureOp_def])
  >- (
    qpat_x_assum` _ = (_,_)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    TOP_CASE_TAC>>fs[]
    >- (
      fs[astTheory.getOpClass_def]>>
      every_case_tac>>fs[]>>
      fs[isPureOp_def])
    >- (
      fs[astTheory.getOpClass_def]>>
      every_case_tac>>fs[]>>
      fs[isPureOp_def])
    >> every_case_tac
    >> gs[state_component_equality,fpState_component_equality, isPureOp_def])
  >- (
    qpat_x_assum` _ = (_,_)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    fs[astTheory.getOpClass_def]>>
    `LENGTH (REVERSE a) = LENGTH es` by
      (imp_res_tac evaluate_length>>
      simp[])>>
    simp[do_app_def]>>
    every_case_tac>>fs[])
  >- (
    qpat_x_assum` _ = (_,_)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    fs[astTheory.getOpClass_def]>>
    `LENGTH (REVERSE a) = LENGTH es` by
      (imp_res_tac evaluate_length>>
      simp[])>>
    simp[do_app_def]>>
    every_case_tac>>fs[])
  >- (every_case_tac>>fs[]>>
    fs[do_log_def]>>every_case_tac>>fs[])
  >- (every_case_tac>>fs[]>>
    fs[do_log_def]>>every_case_tac>>fs[])
  >- (every_case_tac>>fs[]>>
    fs[do_if_def]>>every_case_tac>>fs[])
  >- (every_case_tac>>fs[]>>
    fs[do_if_def]>>every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[]>>
    rfs[]>>
    rveq>>simp[])
  >- (every_case_tac>>fs[]>>
    rfs[]>>
    rveq>>simp[])
  >- (every_case_tac>>fs[]>>
    rfs[]>>
    rveq>>simp[])
  >- (every_case_tac>>fs[]>>
    rfs[]>>
    rveq>>simp[])
  >- (every_case_tac>>fs[])
  >- (every_case_tac>>fs[])
QED

Theorem evaluate_realify_state:
  evaluate st1 env [realify e] = (st2,Rval a) ∧
  isPureExp e ==>
  st1 = st2
Proof
  rw[]>>
  imp_res_tac evaluate_IceFree>>
  fs[markerTheory.Abbrev_def]>>
  fs[isIceFree_def,isPureExp_def]>>
  pop_assum mp_tac>>
  impl_tac >-
    metis_tac[realify_IceFree]>>
  impl_keep_tac >-
    metis_tac[isPureExp_realify]>>
  strip_tac>>
  drule isPureExp_same_ffi>>
  disch_then imp_res_tac>>fs[]>>
  imp_res_tac evaluate_fp_opts_inv >>
  fs[state_component_equality,fpState_component_equality] >>
  simp[FUN_EQ_THM]
QED

(**
  Proofs that the currently supported optimisations are real-valued
  identities. This allows us to establish a relation on the roundoff
  error of the real-valued semantics of the initial program, and
  the floating-point semantics of the optimised program later
**)
Theorem fp_same_sub_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_same_sub] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_same_sub_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ rpt strip_tac \\ rveq
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  \\ ‘∃ choices r. evaluate st1 env [realify e1] = (st1 with fp_state := st1.fp_state with choices := choices, Rval [Real r])’
    by (
    qspecl_then [‘e1’, ‘env’] mp_tac
    (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates_real)
    \\ impl_tac
    >- (gs[isFpArithExp_def, freeVars_real_bound_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ disch_then $ qspec_then ‘st1’ strip_assume_tac
    \\ gs[state_component_equality,fpState_component_equality])
  \\ simp[evaluate_def, realify_def, astTheory.getOpClass_def, do_app_def]
  \\ first_x_assum $ mp_then Any mp_tac $ CONJUNCT1 evaluate_add_choices
  \\ disch_then $ qspec_then ‘choices’ assume_tac \\ gs[]
  \\ ‘st1 with <|refs := st1.refs; ffi := st1.ffi|> = st1’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ fs[EVAL “fp64_to_real 0w”]
  \\ ‘float_to_real <|Sign := 0w: word1; Exponent := 0w: word11; Significand := 0w: 52 word|> = 0’
    by fs[float_to_real]
  \\ rw[]
  \\ fs[state_component_equality, fpState_component_equality]
  \\ fs[realOpsTheory.real_bop_def, floatToRealTheory.getRealBop_def]
QED

Theorem fp_neg_times_minus_one_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_neg_times_minus_one] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_neg_times_minus_one_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def,
          evaluate_case_case, do_app_def]
  \\ ntac 2 (TOP_CASE_TAC \\ gs[])
  \\ ‘q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ ‘st1 with <|refs := st1.refs; ffi := st1.ffi|> = st1’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ Cases_on ‘v’ \\ gs[] \\ rpt strip_tac \\ rveq \\ gs[]
  \\ gs[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ gs[state_component_equality, fpState_component_equality]
  \\ gs[machine_ieeeTheory.fp64_to_real_def, float_to_real_def, realOpsTheory.real_uop_def,
        realOpsTheory.real_bop_def, getRealUop_def, getRealBop_def,
        machine_ieeeTheory.fp64_to_float_def]
  \\ gs[realTheory.real_div, realTheory.REAL_MUL_LZERO, realTheory.REAL_ADD_RID,
        realTheory.REAL_MUL_RID, realTheory.REAL_MUL_RINV, realTheory.REAL_MUL_RNEG]
QED

Theorem fp_neg_times_minus_one_real_id_unfold =
        SIMP_RULE std_ss [icing_optimisationsTheory.fp_neg_times_minus_one_def,
                          reverse_tuple_def, fp_times_minus_one_neg_def]
                  fp_neg_times_minus_one_real_id;

Theorem fp_times_two_to_add_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_times_two_to_add] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_times_two_to_add_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def,
          evaluate_case_case, do_app_def]
  \\ ntac 4 (TOP_CASE_TAC \\ gs[])
  \\ ‘q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ ‘st1 = q ∧ q = q'’ by (imp_res_tac evaluate_realify_state  \\ gs[isPureExp_def])
  \\ rveq \\ gs[] \\ rveq
  \\ Cases_on ‘v’ \\ gs[] \\ rpt strip_tac \\ rveq
  \\ gs[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘q with <|refs := q.refs; ffi := q.ffi|> = q’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ gs[state_component_equality, fpState_component_equality] \\ rpt strip_tac
  \\ rveq \\ gs[]
  \\ gs[EVAL “fp64_to_real 0x4000000000000000w”]
  \\ gs[machine_ieeeTheory.fp64_to_real_def, float_to_real_def, realOpsTheory.real_uop_def,
        realOpsTheory.real_bop_def, getRealUop_def, getRealBop_def,
        machine_ieeeTheory.fp64_to_float_def]
  \\ gs[realTheory.REAL_MUL_LZERO, realTheory.REAL_ADD_RID,
        realTheory.REAL_MUL_RID, realTheory.REAL_MUL_RINV, realTheory.REAL_MUL_RNEG, REAL_OF_NUM_POW]
  \\ RealArith.REAL_ASM_ARITH_TAC
QED

Theorem fp_times_two_to_add_real_id_unfold =
        SIMP_RULE std_ss [icing_optimisationsTheory.fp_times_two_to_add_def]
                  fp_times_two_to_add_real_id;

Theorem fp_times_three_to_add_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_times_three_to_add] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_times_three_to_add_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def,
          evaluate_case_case, do_app_def]
  \\ ntac 6 (TOP_CASE_TAC \\ gs[])
  \\ ‘q''.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ ‘st1 = q ∧ q = q' ∧ q' = q''’
    by (imp_res_tac evaluate_realify_state  \\ gs[isPureExp_def])
  \\ rveq \\ gs[] \\ rveq
  \\ Cases_on ‘v’ \\ gs[] \\ rpt strip_tac \\ rveq
  \\ gs[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘q with <|refs := q.refs; ffi := q.ffi|> = q’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ gs[state_component_equality, fpState_component_equality] \\ rpt strip_tac
  \\ rveq \\ gs[]
  \\ gs[machine_ieeeTheory.fp64_to_real_def, float_to_real_def, realOpsTheory.real_uop_def,
        realOpsTheory.real_bop_def, getRealUop_def, getRealBop_def,
        machine_ieeeTheory.fp64_to_float_def]
  \\ gs[realTheory.real_div, realTheory.REAL_MUL_LZERO, realTheory.REAL_ADD_RID,
        realTheory.REAL_MUL_RID, realTheory.REAL_MUL_RINV, realTheory.REAL_MUL_RNEG]
  \\ RealArith.REAL_ASM_ARITH_TAC
QED

Theorem fp_times_three_to_add_real_id_unfold =
        SIMP_RULE std_ss [icing_optimisationsTheory.fp_times_three_to_add_def]
                  fp_times_three_to_add_real_id;

Theorem fp_times_minus_one_neg_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_times_minus_one_neg] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_times_minus_one_neg_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def,
          evaluate_case_case, do_app_def]
  \\ ntac 2 (TOP_CASE_TAC \\ gs[])
  \\ ‘q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ ‘st1 = q’
    by (imp_res_tac evaluate_realify_state  \\ gs[isPureExp_def])
  \\ rveq \\ gs[] \\ rveq
  \\ Cases_on ‘v’ \\ gs[] \\ rpt strip_tac \\ rveq
  \\ gs[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘q with <|refs := q.refs; ffi := q.ffi|> = q’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ gs[state_component_equality, fpState_component_equality] \\ rpt strip_tac
  \\ rveq \\ gs[]
  \\ gs[machine_ieeeTheory.fp64_to_real_def, float_to_real_def, realOpsTheory.real_uop_def,
        realOpsTheory.real_bop_def, getRealUop_def, getRealBop_def,
        machine_ieeeTheory.fp64_to_float_def]
  \\ gs[realTheory.real_div, realTheory.REAL_MUL_LZERO, realTheory.REAL_ADD_RID,
        realTheory.REAL_MUL_RID, realTheory.REAL_MUL_RINV, realTheory.REAL_MUL_RNEG]
  \\ RealArith.REAL_ASM_ARITH_TAC
QED

Theorem fp_times_minus_one_neg_real_id_unfold =
        SIMP_RULE std_ss [icing_optimisationsTheory.fp_times_minus_one_neg_def]
                  fp_times_minus_one_neg_real_id;

Theorem fp_comm_gen_real_id:
  ∀ fpBop st1 st2 env e r.
  fpBop ≠ FP_Sub ∧
  fpBop ≠ FP_Div ⇒
  is_real_id_exp [fp_comm_gen fpBop] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspecl_then [`e`, `fpBop`] strip_assume_tac
                 (ONCE_REWRITE_RULE [DISJ_COMM] fp_comm_gen_cases)
  >- fs[state_component_equality,fpState_component_equality] >>
  fs[floatToRealTheory.realify_def,evaluate_def,astTheory.getOpClass_def] >>
  qpat_x_assum`_=(_,Rval r)` mp_tac>>
  simp[evaluate_case_case]>>
  ntac 4 (TOP_CASE_TAC>>simp[])>>
  rveq>>fs[isPureExp_def]>>
  imp_res_tac evaluate_realify_state >>
  rveq>>simp[]>>
  imp_res_tac evaluate_sing>>fs[]>>
  Cases_on`fpBop`>>fs[floatToRealTheory.getRealBop_def,do_app_def]>>
  every_case_tac>>simp[state_component_equality,fpState_component_equality] >>
  simp[realOpsTheory.real_bop_def] >>
  metis_tac[realTheory.REAL_ADD_COMM]
QED

Theorem fp_comm_gen_real_id_unfold_add = SIMP_RULE std_ss [fp_bop_distinct, icing_optimisationsTheory.fp_comm_gen_def] (Q.SPEC ‘FP_Add’ fp_comm_gen_real_id);
Theorem fp_comm_gen_real_id_unfold_mul = SIMP_RULE std_ss [fp_bop_distinct, icing_optimisationsTheory.fp_comm_gen_def] (Q.SPEC ‘FP_Mul’ fp_comm_gen_real_id);

Theorem fp_assoc_gen_real_id:
  ∀ fpBop st1 st2 env e r.
    fpBop ≠ FP_Sub ∧
    fpBop ≠ FP_Div ⇒
    is_real_id_exp [fp_assoc_gen fpBop] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ simp[is_rewriteFPexp_correct_def] \\ rpt strip_tac
  \\ qspecl_then [‘e’, ‘fpBop’] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_assoc_gen_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality] >>
  fs[floatToRealTheory.realify_def,evaluate_def,astTheory.getOpClass_def] >>
  qpat_x_assum`_=(_,Rval r)` mp_tac>>
  simp[evaluate_case_case]>>
  ntac 4 (TOP_CASE_TAC>>simp[])>>
  IF_CASES_TAC>>simp[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  simp[do_app_def]>>
  Cases_on`v`>>fs[]>>
  Cases_on`v'`>>fs[]>>
  simp[evaluate_case_case]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  `q' with <|refs := q'.refs; ffi := q'.ffi|> = q'` by
    fs[state_component_equality,fpState_component_equality] >>
  fs[]>>
  IF_CASES_TAC>>simp[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  Cases_on`v`>>rveq>>fs[]>>
  strip_tac>>rveq>>simp[]>>
  simp[state_component_equality,fpState_component_equality]>>
  EVAL_TAC>>simp[]>>
  Cases_on`fpBop`>>fs[floatToRealTheory.getRealBop_def] >>
  metis_tac[realTheory.REAL_ADD_ASSOC]
QED

Theorem fp_assoc_gen_real_id_unfold_add = SIMP_RULE std_ss [fp_bop_distinct, icing_optimisationsTheory.fp_assoc_gen_def] (Q.SPEC ‘FP_Add’ fp_assoc_gen_real_id);
Theorem fp_assoc_gen_real_id_unfold_mul = SIMP_RULE std_ss [fp_bop_distinct, icing_optimisationsTheory.fp_assoc_gen_def] (Q.SPEC ‘FP_Mul’ fp_assoc_gen_real_id);

Theorem fp_assoc2_gen_real_id:
  ∀ fpBop st1 st2 env e r.
    fpBop ≠ FP_Sub ∧
    fpBop ≠ FP_Div ⇒
    is_real_id_exp [fp_assoc2_gen fpBop] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspecl_then [‘e’, ‘fpBop’] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_assoc2_gen_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality]
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  \\ qpat_x_assum ‘_ = (_, Rval r)’ mp_tac
  \\ simp[evaluate_case_case]
  \\ ntac 6 (TOP_CASE_TAC \\ simp[])
  \\ IF_CASES_TAC \\ simp[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ simp[do_app_def]
  \\ Cases_on ‘v’ \\ fs[CaseEq "option"]
  \\ Cases_on ‘v'’ \\ fs[CaseEq "option"]
  \\ simp[evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ simp[])
  \\ ‘q'' with <|refs := q''.refs; ffi := q''.ffi|> = q''’ by
    fs[state_component_equality,fpState_component_equality]
  \\ fs[]
  \\ strip_tac
  \\ ‘q''.fp_state.real_sem’ by fp_inv_tac
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac
  \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ fs[]
  \\ fs[isPureExp_def]
  \\ fs[evaluate_def]
  \\ TOP_CASE_TAC \\ fs[CaseEq "result"]
  \\ fs[CaseEq "result", CaseEq "list"]
  \\ fs[evaluate_def]
  \\ ‘q' with <|refs := q'.refs; ffi := q'.ffi|> = q'’ by
    fs[state_component_equality,fpState_component_equality]
  \\ ‘isPureExp (realify e1)’ by fs[isPureExp_realify]
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  \\ fs[floatToRealTheory.realify_def]
  \\ fs[CaseEq "result", CaseEq "list", CaseEq "prod"] \\ rveq
  \\ ‘q'³'.fp_state.real_sem’ by fp_inv_tac
  \\ fs[CaseEq "result", CaseEq "list", CaseEq "prod"]
  \\ qexists_tac ‘q''.fp_state.choices’ \\ simp[state_component_equality, fpState_component_equality]
  \\ Cases_on ‘fpBop’ \\ fs[floatToRealTheory.getRealBop_def]
  \\ EVAL_TAC
  >- metis_tac[realTheory.REAL_ADD_ASSOC]
  >- metis_tac[realTheory.REAL_MUL_ASSOC]
QED

Theorem fp_assoc2_gen_real_id_unfold_add =
  SIMP_RULE std_ss [reverse_tuple_def, fp_bop_distinct,
                    icing_optimisationsTheory.fp_assoc_gen_def,
                    icing_optimisationsTheory.fp_assoc2_gen_def]
            (Q.SPEC ‘FP_Add’ fp_assoc2_gen_real_id);
Theorem fp_assoc2_gen_real_id_unfold_mul =
  SIMP_RULE std_ss [fp_bop_distinct, reverse_tuple_def,
                    icing_optimisationsTheory.fp_assoc_gen_def,
                    icing_optimisationsTheory.fp_assoc2_gen_def]
            (Q.SPEC ‘FP_Mul’ fp_assoc2_gen_real_id);

Theorem fma_intro_real_id:
  ∀ st1 st2 env e r.
  is_real_id_exp [fp_fma_intro] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspec_then ‘e’ strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_fma_intro_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality] >>
  fs[floatToRealTheory.realify_def,evaluate_def,astTheory.getOpClass_def] >>
  qpat_x_assum`_=(_,Rval r)` mp_tac>>
  simp[evaluate_case_case]>>
  ntac 6 (TOP_CASE_TAC>>simp[])>>
  IF_CASES_TAC>>simp[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  simp[do_app_def]>>
  Cases_on`v`>>fs[]>>
  Cases_on`v'`>>fs[]>>
  Cases_on`v''`>>fs[]>>
  EVAL_TAC>>simp[]>>
  fs[state_component_equality,fpState_component_equality]
QED

Theorem fp_fma_intro_real_id_unfold = REWRITE_RULE [fp_fma_intro_def] fma_intro_real_id;

Theorem fp_sub_add_real_id:
  ∀ st1 st2 env e r.
   is_real_id_exp [fp_sub_add] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspec_then ‘e’ strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_sub_add_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality] >>
  fs[floatToRealTheory.realify_def,evaluate_def,astTheory.getOpClass_def] >>
  qpat_x_assum`_=(_,Rval r)` mp_tac>>
  simp[evaluate_case_case]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  IF_CASES_TAC>>simp[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  simp[do_app_def]>>
  Cases_on`v`>>fs[]>>
  simp[evaluate_case_case]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  `q with <|refs := q.refs; ffi := q.ffi|> = q` by
    fs[state_component_equality,fpState_component_equality] >>
  fs[]>>
  IF_CASES_TAC>>fs[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  Cases_on`v`>>rveq>>fs[]>>
  EVAL_TAC>>simp[]>>
  fs[state_component_equality,fpState_component_equality]>>
  metis_tac[realTheory.real_sub]
QED

Theorem fp_sub_add_real_id_unfold = REWRITE_RULE [fp_sub_add_def] fp_sub_add_real_id;

Theorem fp_add_sub_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_add_sub] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspec_then ‘e’ strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_sub_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality]
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  \\ qpat_x_assum ‘_ = (_, Rval r)’ mp_tac
  \\ simp[evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ simp[])
  \\ IF_CASES_TAC \\ simp[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ simp[do_app_def]
  \\ Cases_on ‘v’ \\ fs[]
  \\ simp[evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ simp[])
  \\ ‘q.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘v’ \\ fs[] \\ Cases_on ‘v'’ \\ fs[] \\ rveq \\ fs[]
  >- (
  rpt strip_tac
  \\ ‘q with <|refs := q.refs; ffi := q.ffi|> = q’ by fs[state_component_equality,fpState_component_equality]
  \\ fs[] \\ rveq
  \\ fs[state_component_equality,fpState_component_equality]
  \\ EVAL_TAC \\ fs[] \\ metis_tac[realTheory.real_sub]
  )
QED

Theorem fp_add_sub_real_id_unfold =
  REWRITE_RULE [reverse_tuple_def, fp_sub_add_def, fp_add_sub_def]
               fp_add_sub_real_id;

Theorem fp_neg_push_mul_r_real_id:
  ∀ st1 st2 env e r.
   is_real_id_exp [fp_neg_push_mul_r] st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qspec_then ‘e’ strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_neg_push_mul_r_cases)
  \\ fs[]
  >- fs[state_component_equality,fpState_component_equality] >>
  fs[floatToRealTheory.realify_def,evaluate_def,astTheory.getOpClass_def] >>
  qpat_x_assum`_=(_,Rval r)` mp_tac>>
  simp[evaluate_case_case]>>
  ntac 4 (TOP_CASE_TAC>>simp[])>>
  IF_CASES_TAC>>simp[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  simp[do_app_def]>>
  Cases_on`v`>>fs[]>>
  simp[evaluate_case_case]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  `q' with <|refs := q'.refs; ffi := q'.ffi|> = q'` by
    fs[state_component_equality,fpState_component_equality] >>
  fs[]>>
  IF_CASES_TAC>>fs[]>>
  imp_res_tac evaluate_sing>>rveq>>fs[]>>
  Cases_on`v`>>rveq>>fs[]>>
  Cases_on`v'`>>rveq>>fs[]>>
  EVAL_TAC>>simp[]>>
  fs[state_component_equality,fpState_component_equality]>>
  metis_tac[realTheory.REAL_NEG_LMUL,realTheory.REAL_MUL_COMM]
QED

Theorem fp_neg_push_mul_r_real_id_unfold =
        REWRITE_RULE [fp_neg_push_mul_r_def] fp_neg_push_mul_r_real_id;

Theorem fp_times_zero_real_id:
  ∀ st1 st2 env e r e1 st1N r1.
    is_real_id_exp [fp_times_zero] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_times_zero_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[SimpL “$==>”, realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ rpt strip_tac \\ rveq
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  \\ ‘∃ choices r. evaluate st1 env [realify e1] = (st1 with fp_state := st1.fp_state with choices := choices, Rval [Real r])’
    by (
    qspecl_then [‘e1’, ‘env’] mp_tac
    (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates_real)
    \\ impl_tac
    >- (gs[isFpArithExp_def, freeVars_real_bound_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ disch_then $ qspec_then ‘st1’ strip_assume_tac
    \\ gs[state_component_equality,fpState_component_equality])
  \\ simp[evaluate_def, realify_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘st1 with <|refs := st1.refs; ffi := st1.ffi|> = st1’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ ‘q with <|refs := q.refs; ffi := q.ffi|> = q’ by fs[state_component_equality]
  \\ fs[] \\ rfs[] \\ fs[]
  \\ fs[EVAL “fp64_to_real 0w”]
  \\ ‘float_to_real <|Sign := 0w: word1; Exponent := 0w: word11; Significand := 0w: 52 word|> = 0’
    by (
    fs[float_to_real]
    )
  \\ rw[]
  \\ fs[state_component_equality, fpState_component_equality]
  \\ fs[realOpsTheory.real_bop_def, floatToRealTheory.getRealBop_def]
QED

Theorem fp_times_zero_real_id_unfold = REWRITE_RULE [fp_times_zero_def] fp_times_zero_real_id;

Theorem fp_distribute_gen_real_id:
  ∀ fpBopOuter fpBopInner st1 st2 env e r.
    fpBopOuter ≠ FP_Mul ∧
    fpBopOuter ≠ FP_Div ∧
    fpBopInner ≠ FP_Add ∧
    fpBopInner ≠ FP_Sub ⇒
    is_real_id_exp [fp_distribute_gen fpBopInner fpBopOuter] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’, ‘fpBopInner’, ‘fpBopOuter’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_distribute_gen_cases)
  \\ fs[]
  \\ rpt strip_tac
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  >- (qexists_tac ‘st2.fp_state.choices’ \\ fs[state_component_equality, fpState_component_equality])
  \\ qpat_x_assum ‘_ = (_, Rval r)’ mp_tac
  \\ simp[evaluate_case_case]
  \\ ntac 6 (TOP_CASE_TAC \\ fs[CaseEq"option"])
  \\ rpt strip_tac \\ rveq \\ fs[]
  \\ fs[do_app_def]
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘v'’ \\ fs[CaseEq"option"] \\ Cases_on ‘v''’ \\ fs[CaseEq"option"]
  \\ ‘q''.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ Cases_on ‘v’ \\ fs[CaseEq"option"]
  \\ ‘q' with <|refs := q'.refs; ffi := q'.ffi|> = q'’ by fs[state_component_equality] \\ fs[]
  \\ fs[isPureExp_def]
  \\ imp_res_tac (GEN_ALL evaluate_realify_state)
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘v’ \\ fs[CaseEq"option"] \\ Cases_on ‘v''’ \\ fs[CaseEq"option"]
  \\ fs[state_component_equality,fpState_component_equality]
  \\ fs[realOpsTheory.real_bop_def, floatToRealTheory.getRealBop_def]
  \\ Cases_on ‘fpBopOuter’ \\ fs[floatToRealTheory.getRealBop_def]
  \\ Cases_on ‘fpBopInner’ \\ fs[floatToRealTheory.getRealBop_def]
  \\ TRY (REAL_ASM_ARITH_TAC)
  \\ metis_tac [realTheory.REAL_ADD_RDISTRIB, realTheory.REAL_SUB_RDISTRIB, realTheory.REAL_DIV_ADD,
                realTheory.real_div]
QED

Theorem fp_distribute_gen_real_id_unfold =
  SIMP_RULE std_ss [fp_bop_distinct, fp_distribute_gen_def] (Q.SPECL [‘FP_Add’, ‘FP_Mul’] fp_distribute_gen_real_id);

Theorem fp_undistribute_gen_real_id:
∀ fpBopOuter fpBopInner st1 st2 env e r.
    fpBopOuter ≠ FP_Mul ∧
    fpBopOuter ≠ FP_Div ∧
    fpBopInner ≠ FP_Add ∧
    fpBopInner ≠ FP_Sub ⇒
    is_real_id_exp [fp_undistribute_gen fpBopInner fpBopOuter] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’, ‘fpBopInner’, ‘fpBopOuter’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_undistribute_gen_cases)
  \\ fs[]
  \\ rpt strip_tac
  \\ fs[floatToRealTheory.realify_def, evaluate_def, astTheory.getOpClass_def]
  >- (qexists_tac ‘st2.fp_state.choices’ \\ fs[state_component_equality, fpState_component_equality])
  \\ qpat_x_assum ‘_ = (_, Rval r)’ mp_tac
  \\ simp[evaluate_case_case]
  \\ ntac 6 (TOP_CASE_TAC \\ fs[CaseEq"option"])
  \\ rpt strip_tac \\ rveq \\ fs[]
  \\ fs[do_app_def]
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘v’ \\ fs[CaseEq"option"] \\ Cases_on ‘v'’ \\ fs[CaseEq"option"]
  \\ ‘q' with <|refs := q'.refs; ffi := q'.ffi|> = q'’ by fs[state_component_equality] \\ fs[]
  \\ fs[isPureExp_def]
  \\ imp_res_tac (GEN_ALL evaluate_realify_state) \\ rveq \\ fs[]
  \\ Cases_on ‘evaluate q env [realify e2]’ \\ fs[] \\ rveq \\ fs[]
  \\ Cases_on ‘evaluate q env [realify e1]’ \\ fs[CaseEq"option"]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘r'³'’ \\ fs[CaseEq"option"]
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ Cases_on ‘v''’ \\ fs[CaseEq"option"] \\ Cases_on ‘v'³'’ \\ fs[CaseEq"option"]
  \\ rveq \\ fs[]
  \\ ‘q' with <|refs := q'.refs; ffi := q'.ffi|> = q'’ by fs[state_component_equality] \\ fs[] \\ rveq
  \\ ‘q'.fp_state.real_sem’ by fp_inv_tac \\ fs[]
  \\ fs[state_component_equality, fpState_component_equality]
  \\ fs[realOpsTheory.real_bop_def, floatToRealTheory.getRealBop_def]
  \\ Cases_on ‘fpBopOuter’ \\ fs[floatToRealTheory.getRealBop_def]
  \\ Cases_on ‘fpBopInner’ \\ fs[floatToRealTheory.getRealBop_def]
  \\ TRY REAL_ASM_ARITH_TAC
  \\ simp[REAL_ADD_LDISTRIB, REAL_SUB_LDISTRIB, real_div]
QED

Theorem fp_undistribute_gen_real_id_unfold =
  SIMP_RULE std_ss [fp_bop_distinct, reverse_tuple_def, fp_distribute_gen_def,
                    fp_undistribute_gen_def]
            (Q.SPECL [‘FP_Add’, ‘FP_Mul’] fp_undistribute_gen_real_id);

Theorem fp_plus_zero_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_plus_zero] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_plus_zero_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ simp[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘st1 with <|refs := st1.refs; ffi := st1.ffi|> = st1’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ ‘st2.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq
  \\ ‘∃ choices r. evaluate st1 env [realify e1] = (st1 with fp_state := st1.fp_state with choices := choices, Rval [Real r])’
    by (
    qspecl_then [‘e1’, ‘env’] mp_tac
    (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates_real)
    \\ impl_tac
    >- (gs[isFpArithExp_def, freeVars_real_bound_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ disch_then $ qspec_then ‘st1’ strip_assume_tac
    \\ gs[state_component_equality,fpState_component_equality])
  \\ gs[] \\ rveq \\ gs[state_component_equality, fpState_component_equality]
  \\ fs[EVAL “fp64_to_real 0w”]
  \\ ‘float_to_real <|Sign := 0w: word1; Exponent := 0w: word11; Significand := 0w: 52 word|> = 0’
    by (
    fs[float_to_real]
    )
  \\ fs[realOpsTheory.real_bop_def, floatToRealTheory.getRealBop_def]
QED

Theorem fp_plus_zero_real_id_unfold = REWRITE_RULE [fp_plus_zero_def] fp_plus_zero_real_id;

Theorem fp_times_one_real_id:
  ∀ st1 st2 env e r.
    is_real_id_exp [fp_times_one] st1 st2 env e r
Proof
  rpt strip_tac
  \\ fs[is_real_id_exp_def]
  \\ qspecl_then [‘e’] strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_times_one_cases)
  \\ fs[state_component_equality,fpState_component_equality]
  \\ rpt strip_tac
  \\ simp[realify_def, evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ ‘st1 with <|refs := st1.refs; ffi := st1.ffi|> = st1’ by fs[state_component_equality]
  \\ pop_assum (fs o single)
  \\ ‘st2.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
  \\ gs[] \\ imp_res_tac evaluate_sing \\ rveq
  \\ ‘∃ choices r. evaluate st1 env [realify e1] = (st1 with fp_state := st1.fp_state with choices := choices, Rval [Real r])’
    by (
    qspecl_then [‘e1’, ‘env’] mp_tac
    (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates_real)
    \\ impl_tac
    >- (gs[isFpArithExp_def, freeVars_real_bound_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ disch_then $ qspec_then ‘st1’ strip_assume_tac
    \\ gs[state_component_equality,fpState_component_equality])
  \\ gs[] \\ rveq \\ gs[state_component_equality, fpState_component_equality]
  \\ fs[EVAL “(fp64_to_real 0x3FF0000000000000w)”]
  \\ fs[EVAL “real_bop (getRealBop FP_Mul) r (float_to_real <|Sign := (0w :word1); Exponent := (1023w :word11); Significand := (0w :52 word)|>)”]
  \\ fs[float_to_real]
  \\ fs[realTheory.real_div, realTheory.REAL_MUL_LZERO, realTheory.REAL_ADD_RID,
        realTheory.REAL_MUL_RID, realTheory.REAL_MUL_RINV]
QED

Theorem fp_times_one_real_id_unfold = REWRITE_RULE [fp_times_one_def] fp_times_one_real_id;

val _ = export_theory();
