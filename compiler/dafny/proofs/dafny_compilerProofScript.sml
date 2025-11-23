(*
  Correctness proof for the Dafny compiler with all of its passes.
*)
Theory dafny_compilerProof
Ancestors
  dafny_semanticPrimitives dafny_evaluateProps
  dafny_freshen dafny_freshenProof
  dafny_remove_assert dafny_remove_assertProof
  dafny_to_cakeml dafny_to_cakemlProof dafny_compiler
  mlstring (* isPrefix *)
  primTypes evaluate semanticPrimitives namespace
  dafny_vcg dafny_vcgProof
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

(* has_main is preserved throughout the compiler passes *)

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

(* -- *)

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

(* Establish no_assert from remove_assert and preserve it throughout the
   compiler passes*)

Definition no_assert_def:
  no_assert (Program members) = EVERY no_assert_member members
End

Theorem no_assert_stmt_remove_assert_stmt[local]:
  ∀stmt. no_assert_stmt (remove_assert_stmt stmt)
Proof
  ho_match_mp_tac remove_assert_stmt_ind
  \\ simp [no_assert_stmt_def, remove_assert_stmt_def]
QED

Theorem no_assert_member_remove_assert_member[local]:
  no_assert_member (remove_assert_member member)
Proof
  Cases_on ‘member’
  \\ simp [no_assert_member_def, remove_assert_member_def]
  \\ simp [no_assert_stmt_remove_assert_stmt]
QED

Theorem no_assert_remove_assert[local]:
  ∀prog. no_assert (remove_assert prog)
Proof
  namedCases ["members"]
  \\ simp [no_assert_def, remove_assert_def]
  \\ Induct_on ‘members’ >- (simp [])
  \\ simp [no_assert_member_remove_assert_member]
QED

Theorem no_assert_member_freshen_member[local]:
  ∀stmt₀ m₀ m₁ m₂ cnt₀ cnt₁ stmt₁.
    no_assert_stmt stmt₀ ∧
    freshen_stmt m₀ m₁ m₂ cnt₀ stmt₀ = (cnt₁, stmt₁) ⇒
    no_assert_stmt stmt₁
Proof
  Induct
  \\ rpt strip_tac
  \\ gvs [freshen_stmt_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [no_assert_stmt_def]
  \\ res_tac \\ simp []
QED

Theorem no_assert_member_freshen_member[local]:
  no_assert_member member ⇒ no_assert_member (freshen_member member)
Proof
  strip_tac
  \\ Cases_on ‘member’
  \\ simp [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [no_assert_member_def]
  \\ drule_all no_assert_member_freshen_member \\ simp []
QED

Theorem no_assert_freshen[local]:
  no_assert prog ⇒ no_assert (freshen_program prog)
Proof
  namedCases_on ‘prog’ ["members"]
  \\ simp [no_assert_def, freshen_program_def]
  \\ Induct_on ‘members’ >- (simp [])
  \\ rpt strip_tac \\ fs []
  \\ drule no_assert_member_freshen_member \\ simp []
QED

(* -- *)

(* Top-level compiler correctness result *)

Theorem correct_compile:
  ∀dfy_ck prog s cml_decs (ffi: 'ffi ffi_state).
    evaluate_program dfy_ck prog = (s, Rcont) ∧
    compile prog = INR cml_decs
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
   ((* has_main *)
    drule_then assume_tac evaluate_program_rcont_has_main
    \\ drule_then assume_tac (iffRL has_main_remove_assert)
    \\ drule_then assume_tac (iffRL has_main_freshen)
    (* no_assert *)
    \\ qspec_then ‘prog’ assume_tac no_assert_remove_assert
    \\ drule_then assume_tac no_assert_freshen
    (* actually valid_prog *)
    \\ namedCases_on ‘prog’ ["members"]
    \\ gvs [valid_prog_def, freshen_program_def, remove_assert_def]
    \\ rpt strip_tac
    >- (simp [every_is_fresh_member_map_freshen_member])
    >- (simp [every_no_shadow_method_freshen_member])
    >- (fs [no_assert_def]))
  >- (* evaluate_prog *)
   (irule correct_freshen_program \\ simp []
    \\ irule correct_remove_assert \\ simp [])
QED

(* TODO move to appropriate place *)
open dafny_evaluateTheory;
open result_monadTheory;
open dafny_wp_calcTheory;

Theorem get_member_aux_rank_methods[local]:
  get_member_aux name members =
    SOME (Method name' ins reqs ens reads decreases outs mods body) ∧
  rank_methods members = INR mets ⇒
  ∃rank.
    MEM
      (Method name'
         <| ins := ins; reqs := reqs; ens := ens; reads := reads;
            decreases := decreases; outs := outs; mods := mods;
            rank := rank |> body) mets
Proof
  cheat
QED

Theorem rank_methods_compatible_env[local]:
  rank_methods members = INR mets ⇒
  compatible_env <| prog := Program members |> (set mets)
Proof
  cheat
QED

open dafny_eval_relTheory;
open dafnyPropsTheory;

Theorem opt_mmap_read_local_every_value_inv:
  ∀names vs.
    OPT_MMAP (read_local s.locals) names = SOME vs ∧
    state_inv s
    ⇒
    EVERY (value_inv s.heap) vs
Proof
  Induct
  \\ simp [PULL_EXISTS]
  \\ rpt strip_tac \\ gvs []
  \\ drule_all read_local_value_inv \\ simp []
QED

open dafny_miscTheory;
Theorem vcg_eval_stmt_imp[local]:
  get_member name prog =
    SOME (Method name' ins reqs ens reads decrs outs mods body) ∧
  (* Method signature (+ specifiation) is ok *)
  dest_Vars mods = INR mod_vars ∧
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  (* VC is ok *)
  vcg prog = INR vcs ∧
  EVERY (λ(vs,p). forall vs p) vcs ∧
  (* arguments are ok *)
  LIST_REL (eval_exp s <| prog := prog |>) args vs ∧
  LENGTH args = LENGTH ins ∧
  (* initial state is ok *)
  Abbrev
    (callee_locals =
     REVERSE
       (ZIP (MAP FST ins,MAP SOME vs) ++
        ZIP (MAP FST outs,REPLICATE (LENGTH outs) NONE))) ∧
  Abbrev
    (callee_s =
     (s with
            <|locals := callee_locals; locals_old := callee_locals;
              heap_old := s.heap; locals_prev := callee_locals;
              heap_prev := s.heap|>)) ∧
  state_inv callee_s ∧
  LIST_REL (mod_loc callee_locals) mod_vars mod_locs ∧
  conditions_hold callee_s <|prog := prog|> reqs ∧
  strict_locals_ok ins callee_locals ∧ locals_ok outs callee_locals
  ⇒
  ∃s'.  (* TODO Add what we learn about s' *)
    eval_stmt s <| prog := prog |>
      (MetCall (MAP (VarLhs ∘ FST) outs) name' args) s' Rcont
Proof
  rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ drule_all_then assume_tac get_member_some_met_name \\ gvs []
  \\ drule_all_then assume_tac eval_exp_evaluate_exps \\ gvs []
  \\ drule_then assume_tac (cj 2 evaluate_exp_add_to_clock) \\ gvs []
  \\ simp [eval_stmt_def, evaluate_stmt_def]
  \\ rename [‘evaluate_exps (s with clock := ck) _’]
  \\ qrefinel [‘_’, ‘1 + ck + ck1’] \\ simp []
  \\ simp [set_up_call_def, safe_zip_def, dec_clock_def]

  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [vcg_def, oneline bind_def, CaseEq "sum"]
  \\ drule_all_then assume_tac mets_vcg_correct
  \\ drule_all_then assume_tac rank_methods_compatible_env
  \\ fs [get_member_def]
  \\ drule_all get_member_aux_rank_methods \\ rpt strip_tac
  \\ drule methods_correct
  \\ disch_then drule \\ gvs []  (* instantiate method *)
  \\ disch_then $
       qspecl_then [
         ‘callee_s’,
         ‘<|prog := Program members|>’,
         ‘mod_locs’ ]
       mp_tac
  \\ simp []
  \\ impl_tac >- (simp [Abbr ‘callee_s’])

  \\ rpt strip_tac
  \\ gvs [eval_stmt_def]
  \\ rename [‘evaluate_stmt (callee_s with clock := ck₂)’]
  \\ cheat

  (* Get past clocks *)
  (* \\ drule evaluate_stmt_add_to_clock \\ gvs [] *)
  (* \\ disch_then $ qspec_then ‘ck₁’ assume_tac *)
  (* \\ dxrule_then assume_tac evaluate_stmt_add_to_clock \\ gvs [] *)
  (* \\ qrefine ‘ck₂ + ck1’ \\ gvs [] *)

  (* Deal with assign *)
  (* \\ fs [GSYM MAP_MAP_o] *)
  (* \\ drule_all_then assume_tac LIST_REL_eval_exp_MAP_Var \\ simp [] *)
  (* \\ drule_all_then assume_tac OPT_MMAP_LENGTH \\ simp [] *)
  (* \\ rename [‘OPT_MMAP (read_local s₁.locals)’] *)
  (* \\ ‘EVERY (λn. IS_SOME (ALOOKUP (restore_caller s₁ s).locals n)) (MAP FST outs)’ by cheat *)
  (* \\ drule IMP_assi_values *)
  (* \\ disch_then drule *)
  (* \\ disch_then $ qspec_then ‘<|prog := Program members|>’ mp_tac *)
  (* \\ impl_tac >- *)
  (*  (simp [restore_caller_def] *)
  (*   \\ drule_all_then assume_tac opt_mmap_read_local_every_value_inv *)
  (*   \\ gvs [state_inv_def] *)
  (*   \\ cheat) *)
  (* \\ rpt strip_tac *)
  (* \\ gvs [assi_values_def, restore_caller_def] *)
QED
