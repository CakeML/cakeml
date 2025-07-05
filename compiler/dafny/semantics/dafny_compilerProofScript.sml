(*
  Correctness proof for the Dafny compiler with all of its passes.
*)

open preamble
open dafny_semanticPrimitivesTheory
open dafny_freshenTheory
open dafny_freshenProofTheory
open dafny_to_cakemlTheory
open dafny_to_cakemlProofTheory
open dafny_compilerTheory
open mlstringTheory  (* isPrefix *)

open danielTheory

val _ = new_theory "dafny_compilerProof";
val _ = set_grammar_ancestry
          ["dafny_semanticPrimitives", "dafny_freshen", "dafny_freshenProof",
           "dafny_to_cakeml", "dafny_to_cakemlProof", "dafny_compiler",
           "mlstring", "daniel"];

Triviality has_main_freshen:
  has_main (Program (MAP freshen_member members)) =
  has_main (Program members)
Proof
  Induct_on ‘members’ \\ simp []
  \\ qx_gen_tac ‘member’
  \\ gvs [has_main_def, get_member_def, get_member_aux_def]
  \\ Cases_on ‘member’ \\ simp [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac UNZIP_LENGTH
  \\ IF_CASES_TAC \\ gvs []
  \\ eq_tac
  \\ rpt strip_tac
  \\ gvs [ZIP_EQ_NIL, UNZIP_EQ_NIL]
QED

Definition valid_members_def:
  valid_members (Program members) =
  EVERY (λmember. ALL_DISTINCT (get_param_names member)) members
End

Triviality map_freshen_member_is_fresh:
  EVERY (λmember. ALL_DISTINCT (get_param_names member)) members ⇒
  EVERY is_fresh_member (MAP freshen_member members)
Proof
  Induct_on ‘members’ \\ simp []
  \\ rpt strip_tac
  \\ irule freshen_member_is_fresh \\ simp []
QED

Triviality map_freshen_member_no_shadow_method:
  EVERY (λmember. ALL_DISTINCT (get_param_names member)) members ⇒
  EVERY no_shadow_method (MAP freshen_member members)
Proof
  Induct_on ‘members’ \\ simp []
  \\ rpt strip_tac
  \\ irule no_shadow_method_freshen_member \\ simp []
QED

Theorem correct_compile:
  ∀dfy_ck prog s' r_dfy cml_decs env_cml (t: 'ffi cml_state).
    evaluate_program dfy_ck T prog = (s', r_dfy) ∧
    compile prog = INR cml_decs ∧
    has_main prog ∧ valid_members prog ∧ has_basic_cons env_cml ∧
    0 < dfy_ck ∧ t.clock = dfy_ck ∧ ExnStamp t.next_exn_stamp = ret_stamp ∧
    r_dfy ≠ Rstop (Serr Rtype_error) ⇒
    ∃ck t' m' r_cml.
      evaluate_decs (t with clock := t.clock + ck) env_cml cml_decs =
        (t', r_cml) ∧
      state_rel m' FEMPTY s' t' env_cml ∧ stmt_res_rel r_dfy r_cml
Proof
  rpt strip_tac
  \\ irule correct_from_program
  \\ fs [compile_def]
  \\ last_assum $ irule_at (Pos last)
  \\ irule_at (Pos last) correct_freshen_program \\ simp []
  \\ namedCases_on ‘prog’ ["members"]
  \\ simp [valid_prog_def, freshen_program_def, has_main_freshen]
  \\ irule_at (Pos hd) map_freshen_member_is_fresh
  \\ irule_at (Pos last) map_freshen_member_no_shadow_method
  \\ fs [valid_members_def]
QED


val _ = export_theory ();
