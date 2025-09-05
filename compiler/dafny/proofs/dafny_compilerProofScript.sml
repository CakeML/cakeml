(*
  Correctness proof for the Dafny compiler with all of its passes.
*)
Theory dafny_compilerProof
Ancestors
  dafny_semanticPrimitives dafny_freshen dafny_freshenProof
  dafny_to_cakeml dafny_to_cakemlProof dafny_compiler
  mlstring (* isPrefix *)
  primTypes evaluate semanticPrimitives namespace
Libs
  preamble


Triviality UNZIP_LENGTH:
  ∀xs ys zs. UNZIP xs = (ys, zs) ⇒ LENGTH ys = LENGTH zs
Proof
  Induct \\ gvs []
QED

Triviality UNZIP_EQ_NIL:
  UNZIP l = ([], []) ⇔ l = []
Proof
  Cases_on ‘l’ \\ gvs []
QED

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

Definition cml_init_state_def:
  cml_init_state ffi ck =
    (FST (THE (prim_sem_env ffi))) with clock := ck
End

Definition cml_init_env_def:
  cml_init_env ffi = (SND (THE (prim_sem_env ffi)))
End

Triviality has_basic_cons_cml_init_env:
  has_basic_cons (cml_init_env ffi)
Proof
  gvs [cml_init_env_def, prim_sem_env_def, prim_types_program_def,
       add_to_sem_env_def, evaluate_decs_def, check_dup_ctors_def,
       combine_dec_result_def, has_basic_cons_def, build_tdefs_def,
       build_constrs_def, extend_dec_env_def, list_type_num_def]
QED

Triviality cml_init_state_next_exn_stamp:
  ExnStamp (cml_init_state ffi ck).next_exn_stamp = ret_stamp
Proof
  gvs [cml_init_state_def, prim_sem_env_def, prim_types_program_def,
       add_to_sem_env_def, evaluate_decs_def, check_dup_ctors_def,
       combine_dec_result_def, has_basic_cons_def, build_tdefs_def,
       build_constrs_def, extend_dec_env_def]
  (* By using rewrite_tac here, we get a more useful proof state (i.e., not just
     F) if the next extension stamp somehow changes in the future. *)
  \\ rewrite_tac [ret_stamp_def] \\ simp []
QED

Triviality cml_init_state_clock:
  (cml_init_state ffi ck).clock = ck
Proof
  gvs [cml_init_state_def]
QED

(* Allows us to irule the correctness theorem for from_program. *)
Triviality cml_init_state_extra_clock:
  cml_init_state ffi (dfy_ck + ck) =
  cml_init_state ffi dfy_ck with clock := (cml_init_state ffi dfy_ck).clock + ck
Proof
  gvs [cml_init_state_def]
QED

Theorem correct_compile:
  ∀dfy_ck prog s' r_dfy cml_decs (ffi: 'ffi ffi_state).
    evaluate_program dfy_ck T prog = (s', r_dfy) ∧
    r_dfy ≠ Rstop (Serr Rtype_error) ∧
    compile prog = INR cml_decs ∧
    has_main prog ∧ valid_members prog
    ⇒
    ∃ck t' m' r_cml.
      evaluate_decs
        (cml_init_state ffi (dfy_ck + ck))
        (cml_init_env ffi) cml_decs = (t', r_cml) ∧
      state_rel m' FEMPTY s' t' (cml_init_env ffi) ∧
      stmt_res_rel r_dfy r_cml
Proof
  rpt strip_tac
  \\ rewrite_tac [cml_init_state_extra_clock]
  \\ irule correct_from_program \\ simp []
  \\ irule_at Any has_basic_cons_cml_init_env
  \\ irule_at Any cml_init_state_next_exn_stamp
  \\ simp [cml_init_state_clock]
  \\ fs [compile_def]
  \\ last_assum $ irule_at (Pos last)
  \\ irule_at (Pos last) correct_freshen_program \\ simp []
  \\ namedCases_on ‘prog’ ["members"]
  \\ simp [valid_prog_def, freshen_program_def, has_main_freshen]
  \\ irule_at (Pos hd) map_freshen_member_is_fresh
  \\ irule_at (Pos last) map_freshen_member_no_shadow_method
  \\ fs [valid_members_def]
QED
