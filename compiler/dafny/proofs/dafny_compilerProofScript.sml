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


Theorem UNZIP_LENGTH[local]:
  ∀xs ys zs. UNZIP xs = (ys, zs) ⇒ LENGTH ys = LENGTH zs
Proof
  Induct \\ gvs []
QED

Theorem UNZIP_EQ_NIL[local]:
  UNZIP l = ([], []) ⇔ l = []
Proof
  Cases_on ‘l’ \\ gvs []
QED

Theorem has_main_freshen[local]:
  has_main (freshen_program prog) =
  has_main prog
Proof
  simp [oneline freshen_program_def]
  \\ CASE_TAC \\ rename [‘MAP freshen_member members’]
  \\ Induct_on ‘members’ \\ simp []
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

Theorem map_freshen_member_is_fresh[local]:
  valid_members (Program members) ⇒
  EVERY is_fresh_member (MAP freshen_member members)
Proof
  simp [valid_members_def]
  \\ Induct_on ‘members’ \\ simp []
  \\ rpt strip_tac
  \\ irule freshen_member_is_fresh \\ simp []
QED

Theorem map_freshen_member_no_shadow_method[local]:
  valid_members (Program members) ⇒
  EVERY no_shadow_method (MAP freshen_member members)
Proof
  simp [valid_members_def]
  \\ Induct_on ‘members’ \\ simp []
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

Theorem has_basic_cons_cml_init_env[local]:
  has_basic_cons (cml_init_env ffi)
Proof
  gvs [cml_init_env_def, prim_sem_env_def, prim_types_program_def,
       add_to_sem_env_def, evaluate_decs_def, check_dup_ctors_def,
       combine_dec_result_def, has_basic_cons_def, build_tdefs_def,
       build_constrs_def, extend_dec_env_def, list_type_num_def]
QED

Theorem cml_init_state_next_exn_stamp[local]:
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

Theorem cml_init_state_clock[local]:
  (cml_init_state ffi ck).clock = ck
Proof
  gvs [cml_init_state_def]
QED

(* Allows us to irule the correctness theorem for from_program. *)
Theorem cml_init_state_extra_clock[local]:
  cml_init_state ffi (dfy_ck + ck) =
  cml_init_state ffi dfy_ck with clock := (cml_init_state ffi dfy_ck).clock + ck
Proof
  gvs [cml_init_state_def]
QED

(* -- TODO Move to appropriate place -- *)
Definition remove_assert_stmt_def:
  remove_assert_stmt (Assert _) = Skip ∧
  remove_assert_stmt (Then stmt₁ stmt₂) =
    Then (remove_assert_stmt stmt₁) (remove_assert_stmt stmt₂) ∧
  remove_assert_stmt (If cnd thn els) =
    If cnd (remove_assert_stmt thn) (remove_assert_stmt els) ∧
  remove_assert_stmt (Dec lcl stmt) =
    Dec lcl (remove_assert_stmt stmt) ∧
  remove_assert_stmt (While grd invs decrs mod body) =
    While grd invs decrs mod (remove_assert_stmt body) ∧
  remove_assert_stmt stmt = stmt
End

Definition remove_assert_member_def:
  remove_assert_member (Method name ins req ens reads decreases outs mod body) =
    Method name ins req ens reads decreases outs mod (remove_assert_stmt body) ∧
  remove_assert_member member = member
End

Definition remove_assert_def:
  remove_assert (Program members) =
    Program (MAP remove_assert_member members)
End

Definition compile_def:
  compile dfy = from_program $ freshen_program $ remove_assert dfy
End

open dafny_evaluateTheory;
Theorem all_distinct_member_name_remove_assert[local]:
  ¬ALL_DISTINCT (MAP member_name (MAP remove_assert_member members)) =
  ¬ALL_DISTINCT (MAP member_name members)
Proof
  cheat
QED

Definition env_rel_def:
  env_rel env env' ⇔
    env'.prog = remove_assert env.prog
End

Theorem env_rel_get_member_none[local]:
  env_rel env env' ∧ get_member name env.prog = NONE ⇒
  get_member name env'.prog = NONE
Proof
  cheat
QED

Theorem env_rel_get_member_method[local]:
  env_rel env env' ∧
  get_member name env.prog =
  SOME (Method name' ins req ens rds decrs outs mod body) ⇒
  get_member name env'.prog =
    SOME (Method name' ins req ens rds decrs outs mod (remove_assert_stmt body))
Proof
  cheat
QED

Theorem env_rel_get_member_function[local]:
  env_rel env env' ∧
  get_member name env.prog = r ∧
  r = SOME (Function name' ins res_t req rds decrs body) ⇒
  get_member name env'.prog = r
Proof
  cheat
QED

Theorem env_rel_evaluate_exp[local]:
  (∀s env' e env.
     env_rel env env' ⇒ evaluate_exp s env' e = evaluate_exp s env e) ∧
  (∀s env' es env.
     env_rel env env' ⇒ evaluate_exps s env' es = evaluate_exps s env es)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Lit’] >- (gvs [evaluate_exp_def])
  >~ [‘Var’] >- (gvs [evaluate_exp_def])
  >~ [‘If’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 3 TOP_CASE_TAC \\ simp [])
  >~ [‘UnOp’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘BinOp’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 3 TOP_CASE_TAC \\ gvs []
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ArrLen’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ArrSel’] >-
   (gvs [evaluate_exp_def]
    \\ last_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ last_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘FunCall’] >-
   (gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env.prog’ ["", "member"] \\ simp []
    >- (drule_all_then assume_tac env_rel_get_member_none \\ simp [])
    \\ Cases_on ‘member’ \\ simp []
    >- (drule_all_then assume_tac env_rel_get_member_method \\ simp [])
    >-
     (drule env_rel_get_member_function \\ simp []
      \\ disch_then $ drule_then assume_tac \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ simp []
      \\ ntac 3 TOP_CASE_TAC
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ simp []))
  >~ [‘Forall’] >-
   (last_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def, eval_forall_def])
  >~ [‘Old’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘OldHeap’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘Prev’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘PrevHeap’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘SetPrev’] >-
   (last_x_assum $ drule_then assume_tac \\ gvs [evaluate_exp_def])
  >~ [‘Let’] >-
   (gvs [evaluate_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ IF_CASES_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp []
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘ForallHeap’] >-
   (first_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def]
    \\ ntac 3 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
  >~ [‘[]’] >- (gvs [evaluate_exp_def])
  >~ [‘_::_’] >-
   (first_x_assum $ drule_then assume_tac
    \\ gvs [evaluate_exp_def]
    \\ ntac 2 TOP_CASE_TAC \\ gvs []
    \\ first_x_assum $ drule_then assume_tac \\ simp [])
QED

Theorem correct_remove_assert_stmt:
  ∀s env stmt s' env' r.
    evaluate_stmt s env stmt = (s', r) ∧ env_rel env env' ∧
    r ≠ Rstop (Serr Rtype_error) ∧ r ≠ Rstop (Serr Rtimeout_error) ⇒
    evaluate_stmt s env' (remove_assert_stmt stmt) = (s', r)
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ simp [remove_assert_stmt_def]
  \\ rpt strip_tac
  >~ [‘Skip’] >- (gvs [evaluate_stmt_def])
  >~ [‘Assert’] >-
   (gvs [evaluate_stmt_def, AllCaseEqs()]
    \\ rename [‘Rerr err’] \\ Cases_on ‘err’ \\ gvs [])
  >~ [‘Then’] >- (gvs [evaluate_stmt_def, AllCaseEqs()])
  >~ [‘If’] >-
   (drule_then assume_tac (cj 1 env_rel_evaluate_exp)
    \\ gvs [evaluate_stmt_def, oneline do_cond_def, AllCaseEqs()])
  >~ [‘Dec local’] >-
   (qpat_x_assum ‘evaluate_stmt _ _ _ = _ ’ mp_tac
    \\ simp [evaluate_stmt_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ TOP_CASE_TAC \\ rpt strip_tac \\ gvs [])
  >~ [‘Assign’] >-
   (cheat)
  >~ [‘While’] >-
   (cheat)
  >~ [‘Print’] >-
   (drule_then assume_tac (cj 1 env_rel_evaluate_exp)
    \\ gvs [evaluate_stmt_def])
  >~ [‘MetCall’] >-
   (cheat)
  >~ [‘Return’] >- (gvs [evaluate_stmt_def])
QED

Theorem correct_remove_assert:
  evaluate_program ck prog = (s,Rcont) ⇒
  evaluate_program ck (remove_assert prog) = (s,Rcont)
Proof
  namedCases_on ‘prog’ ["members"]
  \\ simp [remove_assert_def, evaluate_program_def]
  \\ simp [all_distinct_member_name_remove_assert]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [mk_env_def]
  \\ strip_tac
  \\ drule correct_remove_assert_stmt \\ simp [remove_assert_stmt_def]
  \\ disch_then irule
  \\ simp [env_rel_def, remove_assert_def]
QED

Theorem has_main_remove_assert[local]:
  has_main (remove_assert prog) = has_main prog
Proof
  namedCases_on ‘prog’ ["members"]
  \\ simp [remove_assert_def]
  \\ Induct_on ‘members’
  >- (simp [remove_assert_member_def])
  \\ qx_gen_tac ‘member’
  \\ gvs [has_main_def, get_member_def, get_member_aux_def]
  \\ Cases_on ‘member’ \\ simp [remove_assert_member_def]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem valid_members_remove_assert[local]:
  valid_members prog ⇒ valid_members (remove_assert prog)
Proof
  cheat
QED

Definition no_assert_def:
  no_assert (Program members) = EVERY no_assert_member members
End

Theorem remove_assert_no_assert[local]:
  ∀prog. no_assert (remove_assert prog)
Proof
  cheat
QED

Theorem no_assert_freshen[local]:
  no_assert prog ⇒ no_assert (freshen_program prog)
Proof
  cheat
QED

(* -- * -- *)


Theorem correct_compile:
  ∀dfy_ck prog s cml_decs (ffi: 'ffi ffi_state).
    evaluate_program dfy_ck prog = (s, Rcont) ∧
    compile prog = INR cml_decs ∧
    (* TODO Can we infer this from evaluate_program now? *)
    has_main prog ∧
    (* TODO Shouldn't freshen already guarantee this? *)
    valid_members prog
    ⇒
    ∃ck t' m' r_cml.
      evaluate_decs
        (cml_init_state ffi (dfy_ck + ck))
        (cml_init_env ffi) cml_decs = (t', r_cml) ∧
      state_rel m' FEMPTY s t' (cml_init_env ffi) ∧
      stmt_res_rel Rcont r_cml
Proof
  rpt strip_tac
  \\ rewrite_tac [cml_init_state_extra_clock]
  \\ irule correct_from_program \\ simp []
  \\ irule_at Any has_basic_cons_cml_init_env
  \\ irule_at Any cml_init_state_next_exn_stamp
  \\ simp [cml_init_state_clock]
  \\ fs [compile_def]
  \\ last_assum $ irule_at (Pos last)
  \\ conj_tac
  >- (* valid_prog *)
   ((* has_main preserved *)
    drule_then assume_tac (iffRL has_main_remove_assert)
    \\ drule_then assume_tac (iffRL has_main_freshen)
    (* valid_members preserved *)
    \\ drule_then assume_tac valid_members_remove_assert
    (* no_assert *)
    \\ qspec_then ‘prog’ assume_tac remove_assert_no_assert
    \\ drule_then assume_tac no_assert_freshen
    (* start proving valid_prog *)
    \\ namedCases_on ‘prog’ ["members"]
    \\ gvs [valid_prog_def, freshen_program_def, remove_assert_def]
    \\ rpt strip_tac
    >- (irule map_freshen_member_is_fresh \\ simp [])
    >- (irule map_freshen_member_no_shadow_method \\ simp [])
    >- (fs [no_assert_def]))
  >- (* evaluate_prog *)
   (irule correct_freshen_program \\ simp []
    \\ irule correct_remove_assert \\ simp [])
QED
