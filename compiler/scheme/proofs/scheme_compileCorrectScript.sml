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

fun abbrev_conv name tm =
  let
    val v = mk_var(name,type_of tm)
    val def = new_definition(name ^ "_def", mk_eq(v, tm))
  in
    SYM def
  end

Theorem evaluate_decs_scheme_startup =
  “evaluate_decs
     (FST (THE (prim_sem_env ffi)) with clock := ck)
     (SND (THE (prim_sem_env ffi)))
     (scheme_basis_types ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app])”
  |> (SCONV [prim_sem_env_eq] THENC EVAL)
  |> CONV_RULE (PATH_CONV "rrr" (abbrev_conv "brack_env"))

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
