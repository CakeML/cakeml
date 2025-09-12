open preamble;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open scheme_to_cakeProofTheory;
open primSemEnvTheory;
open primTypesTheory;
open ffiTheory;
open semanticsTheory;
open evaluateTheory;
open evaluatePropsTheory;
open semanticPrimitivesTheory;

val _ = new_theory "scheme_compileCorrect";

(* avoid wasting time printing *)
val _  = (max_print_depth := 15);

Definition v_to_string_def:
  v_to_string (SBool F) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#f") [] /\
  v_to_string (SBool T) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#t") [] /\
  v_to_string _ = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "other") []
End

Theorem imp_semantics_prog:
  evaluate_decs (st with clock := ck) env p = (st1, Rval r) ∧
  st1.ffi.io_events = out ⇒
  semantics_prog st env p (Terminate Success out)
Proof
  fs [semantics_prog_def,evaluate_prog_with_clock_def] \\ rw []
  \\ qexists_tac ‘ck’ \\ simp []
QED

Definition start_up_def:
  start_up = scheme_basis_types ++ scheme_basis ++
             [scheme_basis_list; scheme_basis_app]
End

fun abbrev_conv name tm =
  let
    val v = mk_var(name,type_of tm)
    val def = new_definition(name ^ "_def", mk_eq(v, tm))
  in
    SYM def
  end

Theorem evaluate_decs_start_up =
  “evaluate_decs
     (FST (THE (prim_sem_env ffi)) with clock := ck)
     (SND (THE (prim_sem_env ffi)))
     start_up”
  |> (SCONV [prim_sem_env_eq] THENC EVAL)
  |> CONV_RULE (PATH_CONV "rrrlrr" (abbrev_conv "brack_env_v"))
  |> CONV_RULE (PATH_CONV "rrrrlrr" (abbrev_conv "brack_env_c"))

val brack_env_c_def = definition "brack_env_c_def";

Definition brack_env_def:
  brack_env = <|v := brack_env_v; c := brack_env_c|>
End

Theorem every_one_con_check:
  every_exp
    (one_con_check
     (<| v := brack_env_v; c := brack_env_c|> +++
              SND (THE (prim_sem_env st'.ffi))).c)
     (cps_transform prog "k")
Proof
  simp [semanticPrimitivesTheory.extend_dec_env_def]
  \\ rewrite_tac [prim_sem_env_eq, brack_env_def,
                  LIST_CONJ (TypeBase.accessors_of “:'a sem_env”)]
  \\ simp [namespaceTheory.nsAppend_def,brack_env_c_def]
  \\ cheat (* proving the compiler doesn't produce bas conses *)
QED

Theorem steps_eq_FUNPOW_step:
  ∀n s. steps n s = FUNPOW step n s
Proof
  Induct \\ simp [Once steps_def,FUNPOW]
QED

Theorem scheme_imp_cake:
  codegen prog = INR cake_code ∧
  static_scope ∅ prog ∧
  scheme_semantics_prog prog (STerminate res)
  ⇒
  semantics_prog
    (FST (THE (prim_sem_env ffi)))
    (SND (THE (prim_sem_env (ffi:'ffi ffi_state))))
    cake_code (Terminate Success [v_to_string res])
Proof
  rewrite_tac [scheme_semantics_prog_def,codegen_def,APPEND_ASSOC]
  \\ rewrite_tac [GSYM start_up_def] \\ rw []
  \\ irule imp_semantics_prog
  \\ rewrite_tac [evaluate_decs_append]
  \\ simp [evaluate_decs_start_up]
  \\ simp [CaseEq"prod",CaseEq"result",PULL_EXISTS,combine_dec_result_def]
  \\ simp [Once evaluate_decs_def]
  \\ simp [Once evaluate_decs_def]
  \\ simp [astTheory.pat_bindings_def,every_one_con_check]
  \\ fs [steps_eq_FUNPOW_step]
  \\ qabbrev_tac ‘st0 = λ ck.
                  <|clock := ck; refs := [];
                    ffi := (ffi:'ffi ffi_state);
                    next_type_stamp := 5;
                    next_exn_stamp := 4;
                    fp_state :=
                    <|rws := []; opts := (λx. []); choices := 0;
                      canOpt := Strict; real_sem := F|>;
                    eval_state := NONE|>’
  \\ simp []
  \\ simp [evaluate_def,compile_scheme_prog_def,namespaceTheory.nsOptBind_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env [e]’ \\ simp []
  \\ drule value_terminating
  \\ simp [scheme_semanticsPropsTheory.valid_state_cases,
           scheme_semanticsPropsTheory.can_lookup_cases]
  \\ simp [Once scheme_semanticsPropsTheory.valid_cont_cases]
  \\ simp [FEVERY_DEF,pmatch_def]
  \\ simp [Once cont_rel_cases,PULL_EXISTS]
  \\ disch_then $ qspecl_then [‘e’,‘st0 0’,‘env’] mp_tac
  \\ simp [Abbr‘st0’]
  \\ simp [Once cps_rel_cases]
  \\ simp [Abbr‘env’,combine_dec_result_def]
  \\ impl_tac
  >- cheat (* proving envs *)
  \\ strip_tac
  \\ qexists_tac ‘ck’ \\ fs []
  \\ qpat_x_assum ‘_ = (_,Rval [_])’ kall_tac
  \\ gvs [Abbr‘e’,every_one_con_check]
  \\ cheat (* not too bad *)
QED


(*

Theorem add_to_sem_env_THE:
  ! st st' env env' prog .
    (st', env') = THE (add_to_sem_env (st, env) prog)
    ==>
    evaluate_decs st env prog = (st', Rval env')
Proof
  rpt strip_tac
  >> gvs[add_to_sem_env_def]
  >> Cases_on `evaluate_decs st env prog`
  >> Cases_on `r`
  >> gvs[THE_DEF]
  >> CASE_TAC
QED



Theorem eval_scheme_env':
  ! st env .
    (st, env) = THE (prim_sem_env empty_ffi)
    ==>
    evaluate_decs
      (FST (THE (prim_sem_env empty_ffi)))
      (SND (THE (prim_sem_env empty_ffi)))
      (scheme_basis_types ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app]) =
      (st1, test)
Proof
  simp [prim_sem_env_eq] >> EVAL_TAC

max_print_depth := 10

(*

  simp [scheme_basis_types_def]
  simp [Once evaluate_decs_def,check_dup_ctors_def,combine_dec_result_def,
        scheme_basis_def,do_con_check_def,extend_dec_env_def]

  >> EVAL_TAC
  >> simp[scheme_env'_def]
  >> simp[add_to_sem_env_def]
  >> gvs[]
  >> pop_assum $ simp o single o GSYM
  >> rpt (pairarg_tac >> gvs[])
  >> simp[evaluate_decs_append]
  >> CASE_TAC
  >> CASE_TAC
  >> simp[]

  >> CASE_TAC
  >> CASE_TAC
  >> simp[Once evaluate_decs_cons]

  >> CASE_TAC
  >> CASE_TAC
  >> simp[]

  >> CASE_TAC
  >> simp[]
*)
QED

Theorem scheme_semantics_preservation_terminates:
  ! prog cml_prog v st env ffi .
    scheme_semantics_prog prog (STerminate v) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog /\
    (st, env) = THE (prim_sem_env empty_ffi)
    ==>
    semantics_prog st ednv cml_prog (Terminate Success [v_to_string v])
Proof
  (*Somewhere in here, I need a lemma that evaluate st env (...) = (st', Rval scheme_env')*)
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[codegen_def, static_scope_check_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt (pairarg_tac \\ fs [])
  >> SRULE [] scheme_env'_def
  >> extend_dec_env_def
  >> evaluate_decs_append
QED

*)

val _  = (max_print_depth := 0); (* don't print stuff in docs *)
val _ = export_theory();
