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

Definition mods_ok_def:
  mods_ok s_locals mods mod_vars mod_locs ⇔
    (* modifies currently only supports variables *)
    dest_Vars mods = INR mod_vars ∧
    (* mod_vars are locations *)
    LIST_REL (mod_loc s_locals) mod_vars mod_locs
End

Definition vc_ok_def:
  vc_ok prog ⇔
    ∃vcs. vcg prog = INR vcs ∧ EVERY (λ(vs,p). forall vs p) vcs
End

Definition can_read_outs_def:
  can_read_outs s env outs ⇔
    ∃out_vs. LIST_REL (eval_exp s env) (MAP (Var ∘ FST) outs) out_vs
End

Definition state_ok_def:
  state_ok s ins outs ⇔
    s.locals_old = s.locals ∧ s.heap_old = s.heap ∧ state_inv s ∧
    strict_locals_ok ins s.locals ∧ locals_ok outs s.locals
End

Theorem vc_ok_imp[local]:
  vc_ok prog ∧
  get_member name prog =
    SOME (Method name' ins reqs ens reads decrs outs mods body) ∧
  conditions_hold s <| prog := prog |> reqs ∧
  (* (some "technical" conditions) *)
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  mods_ok s.locals mods mod_vars mod_locs ∧
  state_ok s ins outs ∧
  (* compiler stuff *)
  from_stmt body lvl = INR body_cml ∧
  state_rel m l s t env_cml ∧
  base_at_most base t.refs l ∧
  env_rel <| prog := prog |> env_cml ∧
  is_fresh_stmt body ∧
  no_shadow (set (MAP FST s.locals)) body ∧
  no_assert_stmt body
  ⇒
  ∃s' ck ck₁ (t': 'ffi cml_state) m'.
    (* Dafny *)
    eval_stmt s <| prog := prog |> body s' (Rstop Sret) ∧
    valid_mod s.heap (MAP get_loc mod_locs) s'.heap ∧
    conditions_hold s' <| prog := prog |>
      (MAP (wrap_Old (set (MAP FST ins))) ens) ∧
    can_read_outs s' <| prog := prog |> outs ∧
    (* CakeML *)
    evaluate$evaluate (t with clock := ck) env_cml [body_cml] =
      (t', Rerr (Rraise (Conv (SOME ret_stamp) []))) ∧
    store_preserve base t.refs t'.refs ∧
    state_rel m' l (s' with clock := ck₁) t' env_cml ∧ m ⊑ m'
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [vc_ok_def, vcg_def, oneline bind_def, CaseEq "sum"]
  \\ drule_all_then assume_tac rank_methods_compatible_env
  \\ drule_all_then assume_tac mets_vcg_correct
  \\ fs [get_member_def]
  \\ drule_all get_member_aux_rank_methods \\ rpt strip_tac
  \\ drule methods_correct
  \\ disch_then drule \\ simp []
  \\ disch_then $
       qspecl_then
         [‘s’, ‘<|prog := Program members|>’, ‘mod_vars’, ‘mod_locs’] mp_tac
  \\ fs [mods_ok_def, state_ok_def]
  \\ rpt strip_tac
  \\ first_assum $ irule_at (Pos hd)
  \\ simp [can_read_outs_def]
  \\ first_assum $ irule_at (Pos hd)
  \\ gvs [eval_stmt_def]
  \\ drule correct_from_stmt
  \\ disch_then drule
  \\ rename [‘evaluate_stmt (s with clock := ck₁)’]
  \\ disch_then $
       qspecl_then [‘t with clock := ck₁’, ‘env_cml’, ‘m’, ‘l’, ‘base’] mp_tac
  \\ simp []
  \\ impl_tac >- (gvs [state_rel_def])
  \\ rpt strip_tac
  \\ namedCases_on ‘r_cml’ ["v", "err"] \\ gvs [stmt_res_rel_def]
  \\ Cases_on ‘err’ \\ gvs [stmt_res_rel_def]
  \\ first_assum $ irule_at (Pos hd) \\ simp []
  \\ first_assum $ irule_at (Pos hd) \\ simp []
QED
