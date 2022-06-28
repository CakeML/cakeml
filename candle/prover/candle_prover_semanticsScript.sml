(*
  Top-level soundness theorem for the Candle theorem prover.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory candle_kernelProgTheory
open permsTheory candle_kernel_funsTheory candle_kernel_valsTheory
     candle_prover_invTheory candle_prover_evaluateTheory ast_extrasTheory
     candle_basis_evaluateTheory semanticsTheory;
open holKernelProofTheory basisProgTheory ml_hol_kernel_funsProgTheory;
open ml_translatorLib ml_progTheory;
local open ml_progLib in end

val _ = new_theory "candle_prover_semantics";

val _ = set_grammar_ancestry [
  "misc", "semanticPrimitivesProps", "namespaceProps", "evaluate",
   "candle_prover_inv", "candle_basis_evaluate", "candle_kernelProg",
   "semantics" ];

val _ = translation_extends "candle_kernelProg";

Theorem LPREFIX_LNTH:
  ∀n xs l ll.
    LPREFIX xs l ∧
    LNTH n xs = NONE ∧
    LTAKE n l = SOME ll ⇒
      LPREFIX xs (fromList ll)
Proof
  Induct \\ rpt Cases \\ rw [llistTheory.fromList_def]
  \\ gvs [LPREFIX_LCONS, SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * - The basis program:
 *   basis, basis_env, basis_state
 * - The candle program (includes the former):
 *   candle_code, candle_init_env, candle_init_state
 * ------------------------------------------------------------------------- *)

Overload basis_env = (basis_Decls_thm |> concl |> rator |> rand);

Overload basis_state = (basis_Decls_thm |> concl |> rand |> rator);

(* -------------------------------------------------------------------------
 * Show that the basis program satisfies post_state_ok, simple_dec and
 * safe_dec. Use this to show basis_env is env_ok.
 * ------------------------------------------------------------------------- *)

Theorem post_state_ok_basis_state:
  post_state_ok (basis_state ffi)
Proof
  rw [post_state_ok_def, kernel_types_def, kernel_locs_def,
      the_type_constants_def, the_term_constants_def,
      the_axioms_def, the_context_def]
  \\ EVAL_TAC \\ gs []
QED

Theorem basis_decs_ok:
  EVERY simple_dec basis ∧
  EVERY safe_dec basis
Proof
  once_rewrite_tac [basis_def]
  \\ rewrite_tac [simple_dec_simps, EVERY_DEF, safe_dec_simps]
  \\ rpt conj_tac
  \\ TRY (
    EVAL_TAC
    \\ rpt strip_tac
    \\ rveq
    \\ rewrite_tac []
    \\ pop_assum mp_tac
    \\ rewrite_tac [IN_INSERT,namespaceTheory.id_to_n_def,CONS_11,NOT_NIL_CONS,NOT_IN_EMPTY]
    \\ EVAL_TAC
    \\ NO_TAC
  )
QED

Theorem env_ok_basis_env:
  env_ok ctxt basis_env
Proof
  assume_tac basis_Decls_thm
  \\ gs [Decls_def]
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) evaluate_basis_v_ok_decs
  \\ simp [basis_decs_ok, post_state_ok_basis_state, env_ok_init_env]
  \\ impl_tac
  >- (
    simp [init_env_def]
    \\ simp [namespacePropsTheory.nsLookup_Bind_v_some, PULL_EXISTS]
    \\ rw [] \\ gs [kernel_types_def])
  \\ rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some, SF SFY_ss]
QED

(* --------------------------------------------------------------------------
 * Show that the candle_init_state is state_ok.
 * ------------------------------------------------------------------------- *)

(* TODO Move this to standard/ml_kernel; a copy of this is used by the
 *      OpenTheory reader.
 *)

Definition init_refs_def:
  init_refs = <|
      the_type_constants := init_type_constants;
      the_term_constants := init_term_constants;
      the_axioms         := init_axioms;
      the_context        := init_context |>
End

Theorem STATE_init_refs:
  STATE init_context init_refs
Proof
  simp [STATE_def, CONTEXT_def, init_type_constants_def, init_axioms_def,
        init_term_constants_def, init_context_def, init_refs_def,
        holSyntaxTheory.init_ctxt_def, holSyntaxTheory.extends_def]
QED

Theorem candle_init_state_stamp:
  n ∈ kernel_types ⇒ n < (candle_init_state ffi).next_type_stamp
Proof
  EVAL_TAC \\ gs []
QED

Theorem kernel_refs_distinct[local,simp]:
  the_type_constants ≠ the_term_constants ∧
  the_type_constants ≠ the_axioms ∧
  the_type_constants ≠ the_context ∧
  the_term_constants ≠ the_axioms ∧
  the_term_constants ≠ the_context ∧
  the_axioms ≠ the_context
Proof
  simp [the_type_constants_def, the_term_constants_def, the_context_def,
        the_axioms_def]
QED

Theorem LLOOKUPs[local]:
  (Loc loc = the_type_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_type_constants_v)) ∧
  (Loc loc = the_term_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_term_constants_v)) ∧
  (Loc loc = the_axioms ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_axioms_v)) ∧
  (Loc loc = the_context ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_context_v))
Proof
  rpt strip_tac
  \\ gvs [the_type_constants_def, the_term_constants_def, the_axioms_def,
          the_context_def]
  \\ rw [candle_init_state_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
QED

Theorem candle_init_state_refs:
  loc ∈ kernel_locs ⇒
    kernel_loc_ok init_refs loc (candle_init_state ffi).refs
Proof
  gvs [kernel_locs_def, kernel_loc_ok_def]
  \\ rw [] \\ gs []
  \\ FIRST (map (drule_then (qspec_then ‘ffi’ assume_tac))
                (CONJUNCTS LLOOKUPs))
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [init_refs_def, init_type_constants_v_thm, init_term_constants_v_thm,
           init_axioms_v_thm, init_context_v_thm]
QED

Theorem candle_init_state_eval[simp]:
  eval_state_ok (candle_init_state ffi).eval_state
Proof
  EVAL_TAC
QED

Theorem candle_init_state_ffi[simp]:
  (candle_init_state ffi).ffi = ffi
Proof
  EVAL_TAC
QED

Theorem candle_init_state_state_ok:
  ffi.io_events = [] ⇒
  state_ok init_context (candle_init_state ffi)
Proof
  strip_tac
  \\ simp [state_ok_def, candle_init_state_stamp]
  \\ irule_at Any STATE_init_refs
  \\ simp [candle_init_state_refs,kernel_locs]
  \\ rw [LLOOKUP_EQ_EL, EL_APPEND_EQN, candle_init_state_def, refs_defs]
  \\ ‘loc = 0’ by fs []
  \\ fs [ref_ok_def]
QED

(* --------------------------------------------------------------------------
 * First prove that all kernel values are v_ok (this follows from the
 * definition of v_ok but it's nice to have in one theorem.)
 * ------------------------------------------------------------------------- *)

fun prove_v_ok v_tm =
  auto_prove
    ("v_ok for " ^ (#1 (dest_const v_tm)))
    (“v_ok ctxt (^v_tm)”,
     irule v_ok_KernelVals
     \\ irule v_ok_Inferred
     \\ irule inferred_KernelFuns
     \\ simp_tac list_ss [kernel_funs_def]);

Theorem v_ok_kernel_funs[local] =
  kernel_funs_def |> concl |> rhs
  |> pred_setSyntax.strip_set
  |> map prove_v_ok
  |> LIST_CONJ;

(* --------------------------------------------------------------------------
 * Now prove that candle_init_env is env_ok.
 * ------------------------------------------------------------------------- *)

(* Prove env_ok and cache intermediate results. This code is very brittle.
 *)

exception EnvOkExn of term;

local
  (* Constants (can these be found in a syntax file?) *)
  val kernel_types_term = kernel_types_def |> concl |> lhs;
  val kernel_ctors_term = kernel_ctors_def |> concl |> lhs;
  val write_cons_term =
    write_cons_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val v_ok_term = v_ok_def |> CONJUNCT1 |> concl |> lhs |> rator |> rator;
  val write_term =
    write_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val write_mod_term =
    write_mod_def |> SPEC_ALL |> concl |> lhs |> rator |> rator |> rator;
  val merge_env_term = merge_env_def |> SPEC_ALL |> concl |> lhs |> rator
                       |> rator;
  val env_ok_term = env_ok_def |> concl |> lhs |> rator |> rator;
  val init_context_term = init_context_def |> concl |> lhs;
  (* Types *)
  val env_type = env_ok_def |> concl |> lhs |> rand |> type_of;
  val inst_context = INST [“ctxt:update list”|->init_context_term];
  (* Dealing with env_ok terms *)
  fun dest_env_ok tm =
    let
      val (envok_ctxt, env) = dest_comb tm
      val (envok, ctxt) = dest_comb envok_ctxt
      val _ = same_const envok env_ok_term orelse fail ()
      val _ = same_const ctxt init_context_term orelse fail ()
    in
      env
    end
    handle HOL_ERR _ => failwith ("dest_env_ok: not an env_ok")
  fun mk_env_ok tm =
    mk_comb (mk_comb (env_ok_term, init_context_term), tm);
  (* Cache of previously proven theorems *)
  fun insert_term th =
    let
      val th = inst_context th
    in
      Net.insert (dest_env_ok (concl th), th)
    end;
  val empty_net = List.foldl (uncurry insert_term) Net.empty
                             [env_ok_basis_env,
                              env_ok_empty_env,
                              env_ok_nsEmpty];
  val prev_ths = ref empty_net;
  (* 'Prove' v_ok for kernel values by looking them up in the kernel funs
   * theorem from above. *)
  val v_ok_thms = map inst_context (CONJUNCTS v_ok_kernel_funs);
  fun prove_v_ok tm =
    let
      val goal = mk_comb (mk_comb (v_ok_term, init_context_term), tm)
    in
      Lib.first (can (Lib.C match_term goal) o concl) v_ok_thms
    end;
  (* Theorems *)
  val write_th = inst_context env_ok_write |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val merge_env_th = inst_context env_ok_merge_env
                     |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_mod_th = inst_context env_ok_write_mod
                     |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_cons_th = inst_context env_ok_write_cons
                      |> REWRITE_RULE [GSYM AND_IMP_INTRO];
  val write_exn_th = inst_context env_ok_write_Exn
  (* Conversion *)
  fun prove_bare tm = (* bare environment *)
    let
      val {Name, Thy, Ty} = dest_thy_const tm
      val _ = Ty = env_type orelse failwith "not an env"
      val defn = fetch Thy (Name ^ "_def")
      val th = iffRL (AP_TERM “env_ok init_context” defn)
      val (subgoal, _) = dest_imp (concl th)
      val th' = env_ok_conv subgoal
    in
      MATCH_MP th th'
    end
  and prove_merge_env tm = (* merge_env e1 e2 *)
    let
      val (me1, e2) = dest_comb tm
      val (me, e1) = dest_comb me1
      val _ = same_const me merge_env_term orelse
              failwith "not merge_env"
      val sg1 = mk_env_ok e1
      val sg2 = mk_env_ok e2
      val th1 = env_ok_conv sg1
      val th2 = env_ok_conv sg2
    in
      MATCH_MP (MATCH_MP merge_env_th th1) th2
    end
  and prove_write_mod tm = (* write_mod mn env1 env2 *)
    let
      val (wmmne1, e2) = dest_comb tm
      val (wmmn, e1) = dest_comb wmmne1
      val (wm, mn) = dest_comb wmmn
      val _ = same_const wm write_mod_term orelse
              failwith "not write_mod"
      val sg1 = mk_env_ok e1
      val sg2 = mk_env_ok e2
      val th1 = env_ok_conv sg1
      val th2 = env_ok_conv sg2
    in
      INST [“mn:string”|->mn] (MATCH_MP (MATCH_MP write_mod_th th1) th2)
    end
  and prove_write tm = (* write nm v env *)
    let
      val (wnv, env) = dest_comb tm
      val (wn, v) = dest_comb wnv
      val (w, n) = dest_comb wn
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val th2 = prove_v_ok v
    in
      INST [“nm:string”|->n] (MATCH_MP (MATCH_MP write_th th1) th2)
    end
  and prove_write_cons tm = (* write_cons n (TypeStamp s t) env *)
    let
      val (wcns, env) = dest_comb tm
      val (wcn, s) = dest_comb wcns
      val (wc, n) = dest_comb wcn
      val _ = same_const wc write_cons_term orelse
              failwith "not write_cons"
      val m = dest_pair s |> #1
      val t = dest_pair s |> #2 |> rand
      val nm = dest_pair s |> #2 |> rator |> rand
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val goal =
        mk_imp (pred_setSyntax.mk_in (t, kernel_types_term),
                pred_setSyntax.mk_in (nm, kernel_ctors_term))
      val th2 = SIMP_CONV list_ss [kernel_types_def, kernel_ctors_def] goal
      val th3 =
        INST [“n:num”|->m, “s:string”|->nm, “t:num”|->t, “nm:string”|->n]
             (MATCH_MP write_cons_th th1)
    in
      MATCH_MP th3 (EQT_ELIM th2)
    end
  and prove_write_Exn tm = (* write_cons n (ExnStamp ...) env *)
    (* FIXME This can succeed if it's given a term with TypeStamp *)
    let
      val (wcns, env) = dest_comb tm
      val (wcn, s) = dest_comb wcns
      val (wc, n) = dest_comb wcn
      val _ = same_const wc write_cons_term orelse
              failwith "not write_cons"
      val sg1 = mk_env_ok env
      val th1 = env_ok_conv sg1
      val m = s |> dest_pair |> #2 |> rand
      val k = s |> dest_pair |> #1
    in
      INST [“n:num”|->k, “m:num”|->m, “nm:string”|->n]
           (MATCH_MP write_exn_th th1)
    end
  and env_ok_conv tm =
    let
      val env_tm = dest_env_ok tm
      fun prove env_tm =
          let
            fun prover env_tm =
              prove_bare env_tm handle HOL_ERR _ =>
              prove_merge_env env_tm handle HOL_ERR _ =>
              prove_write_mod env_tm handle HOL_ERR _ =>
              prove_write env_tm handle HOL_ERR _ =>
              prove_write_cons env_tm handle HOL_ERR _ =>
              prove_write_Exn env_tm handle HOL_ERR _ =>
                raise EnvOkExn tm
            val th = prover env_tm
          in
            prev_ths := Net.insert (env_tm, th) (!prev_ths);
            th
          end
    in
      case Net.match env_tm (!prev_ths) of
        th::_ => th
      | _ => prove env_tm
    end;
in
  fun reset_cache () = prev_ths := empty_net;
  fun get_cache () = Net.listItems (!prev_ths)
  val prove_env_ok = EQT_INTRO o env_ok_conv
end

Theorem env_ok_candle_init_env:
  env_ok init_context candle_init_env
Proof
  CONV_TAC prove_env_ok
QED

(* --------------------------------------------------------------------------
 * Top-level semantics theorem.
 * ------------------------------------------------------------------------- *)

(* TODO Print context updates on FFI
    -- Magnus: actually, we might want to print the entire context
               for each theorem to make soundness statement simple
   TODO: Use 'ffi
 *)

(* TODO why do these both exist? *)

Theorem init_context_init_ctxt[local,simp]:
  init_ctxt = init_context
Proof
  rw [holSyntaxTheory.init_ctxt_def, init_context_def]
QED

Theorem semantics_thm:
  semantics_prog (init_state ffi with eval_state := es)
                 init_env (candle_code ++ prog) res ∧
  eval_state_ok es ∧
  EVERY safe_dec prog ∧
  ffi.io_events = [] ∧
  res ≠ Fail ⇒
    (∀outcome io_list.
       res = Terminate outcome io_list ⇒
         EVERY ok_event io_list) ∧
    (∀io_trace.
       res = Diverge io_trace ⇒
         every ok_event io_trace)
Proof
  strip_tac
  \\ Cases_on ‘res’ \\ gs []
  >~ [‘Terminate outcome io_list’] >- (
    gs [semantics_prog_def]
    \\ gs [evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ gvs []
    \\ assume_tac candle_prog_thm
    \\ dxrule_then (qspec_then ‘es’ mp_tac) Decls_set_eval_state
    \\ rw [Once init_state_def]
    \\ gvs [evaluate_decs_append, CaseEqs ["prod", "semanticPrimitives$result"]]
    >- (
      gs [ml_progTheory.Decls_def]
      \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
      \\ qpat_x_assum ‘evaluate_decs _ _ _ = (s1, Rval _)’ assume_tac
      \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
      \\ rw []
      \\ qpat_x_assum ‘evaluate_decs s1 _ prog = _’ assume_tac
      \\ drule_then (qspec_then ‘init_context’ mp_tac)
                    (el 3 (CONJUNCTS evaluate_v_ok))
      \\ impl_tac
      >- (
        drule_then assume_tac candle_init_state_state_ok
        \\ assume_tac env_ok_candle_init_env \\ gs []
        \\ irule_at Any env_ok_extend_dec_env \\ gs [env_ok_init_env]
        \\ gs [state_ok_def, semanticPrimitivesTheory.state_component_equality]
        \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
      \\ strip_tac
      \\ rename1 ‘combine_dec_result _ res’ \\ Cases_on ‘res’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [ml_progTheory.Decls_def]
    \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
    \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
    \\ rw [] \\ gs [CaseEqs ["semanticPrimitives$result"]])
  \\ gs [semanticsTheory.semantics_prog_def]
  \\ qmatch_asmsub_abbrev_tac`IMAGE ff`
  \\ drule lprefix_lub_is_chain \\ strip_tac
  \\ rw[every_LNTH]
  \\ Cases_on`∃p. p ∈ IMAGE ff UNIV ∧ LNTH n p <> NONE` \\ gs[]
  >- (
    rename1`LNTH n (ff k) <> NONE`
    \\ `∃v. LNTH n (ff k) = SOME v` by metis_tac[option_CASES]
    \\ first_x_assum (qspec_then ‘k’ (qx_choose_then ‘ffi1’ assume_tac))
    \\ gs [Abbr ‘ff’, evaluate_prog_with_clock_def]
    \\ rename1 ‘LNTH n l = SOME w’
    \\ ‘v = w’
      by (gs [lprefix_lub_def, LPREFIX_NTH, LNTH_fromList]
          \\ gs[PULL_EXISTS, less_opt_def]
          \\ last_x_assum(qspec_then`k`mp_tac) \\ simp[LNTH_fromList]
          \\ disch_then (qspec_then ‘n’ assume_tac) \\ gs [])
    \\ pairarg_tac \\ gvs []
    \\ assume_tac candle_prog_thm
    \\ dxrule_then (qspec_then ‘es’ mp_tac) Decls_set_eval_state
    \\ rw [Once init_state_def]
    \\ gs [Decls_def]
    \\ gvs [evaluate_decs_append, CaseEqs ["semanticPrimitives$result", "prod"], combine_dec_result_def]
    >- (
      dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
      \\ qpat_x_assum ‘evaluate_decs _ _ candle_code = _’ assume_tac
      \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
      \\ rw []
      \\ qpat_x_assum ‘evaluate_decs _ _ prog = _’ assume_tac
      \\ drule_then (qspec_then ‘init_context’ mp_tac)
                    (el 3 (CONJUNCTS evaluate_v_ok))
      \\ impl_tac
      >- (
        drule_then assume_tac candle_init_state_state_ok
        \\ assume_tac env_ok_candle_init_env \\ gs []
        \\ irule_at Any env_ok_extend_dec_env \\ gs [env_ok_init_env]
        \\ gs [state_ok_def, semanticPrimitivesTheory.state_component_equality]
        \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
      \\ strip_tac \\ gs []
      \\ gvs [LNTH_fromList, EVERY_EL])
    \\ ‘k ≤ ck1’
      by (dxrule_then drule evaluatePropsTheory.evaluate_decs_clock_determ
          \\ rw [])
    \\ drule_then (qspecl_then [‘init_state ffi with eval_state := es’,‘init_env’,‘candle_code’]
                  mp_tac)
                  evaluate_decs_ffi_mono_clock
    \\ rw [io_events_mono_def] \\ gs [])
  \\ `lprefix_chain_nth n (IMAGE ff UNIV) = NONE`
  by (
    irule not_exists_lprefix_chain_nth
    \\ simp[PULL_EXISTS]
    \\ metis_tac[])
  \\ drule lprefix_lub_nth
  \\ disch_then(qspec_then`l`mp_tac) \\ simp[]
  \\ disch_then(qspec_then`n`mp_tac) \\ simp[]
QED

Definition events_of_def:
  events_of (Terminate _ io_list) = set io_list ∧
  events_of (Diverge io_llist) = LSET io_llist ∧
  events_of Fail = 𝕌(:io_event)
End

Theorem events_of_semantics:
  semantics_prog (init_state ffi) init_env (candle_code ++ prog) res ∧
  EVERY safe_dec prog ∧ ffi.io_events = [] ∧ res ≠ Fail ⇒
  ∀e. e IN events_of res ⇒ ok_event e
Proof
  rw [IN_DEF]
  \\ ‘init_state ffi = init_state ffi with eval_state := NONE’
    by rw [init_state_def]
  \\ pop_assum SUBST_ALL_TAC
  \\ ‘eval_state_ok NONE’ by gs [eval_state_ok_def]
  \\ drule_all semantics_thm
  \\ Cases_on ‘res’ \\ fs [events_of_def]
  \\ fs [every_LNTH,LSET_def,EVERY_MEM,IN_DEF] \\ rw []
  \\ res_tac
QED

Theorem events_of_semantics_with_eval_state:
  semantics_prog (init_state ffi with eval_state := ev)
    init_env (candle_code ++ prog) res ∧ eval_state_ok ev ∧
  EVERY safe_dec prog ∧ ffi.io_events = [] ∧ res ≠ Fail ⇒
  ∀e. e IN events_of res ⇒ ok_event e
Proof
  strip_tac
  \\ drule_all semantics_thm
  \\ Cases_on ‘res’ \\ fs [events_of_def]
  \\ fs [every_LNTH,LSET_def,EVERY_MEM,IN_DEF] \\ rw []
  \\ res_tac
QED

val _ = export_theory ();
