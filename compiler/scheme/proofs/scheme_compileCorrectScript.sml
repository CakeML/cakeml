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

Definition v_to_string_def:
  v_to_string (SBool F) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#f") [] /\
  v_to_string (SBool T) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#t") [] /\
  v_to_string _ = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "other") []
End

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
    evaluate_decs st env (scheme_basis_types ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app]) = (st, Rval scheme_env')
Proof
  rpt strip_tac
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
QED

Theorem scheme_semantics_preservation_terminates:
  ! prog cml_prog v st env ffi .
    scheme_semantics_prog prog (STerminate v) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog /\
    (st, env) = THE (prim_sem_env empty_ffi)
    ==>
    semantics_prog st env cml_prog (Terminate Success [v_to_string v])
Proof
  (*Somewhere in here, I need a lemma that evaluate st env (...) = (st', Rval scheme_env')*)
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[codegen_def, static_scope_check_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt strip_tac
  >> SRULE [] scheme_env'_def
  >> extend_dec_env_def
  >> evaluate_decs_append
QED

val _ = export_theory();
