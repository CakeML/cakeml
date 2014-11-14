open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib;
open infer_eSoundTheory;
open infer_eCompleteTheory;

val _ = new_theory "type_eDeterm";

val _ = temp_tight_equality ();

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 rw [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

val infer_e_type_e_determ = Q.store_thm ("infer_e_type_e_determ",
`!menv cenv env tenv e st t.
  check_menv menv ∧
  tenvC_ok cenv ∧
  check_env {} env ∧
  tenv_invC FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  check_t 0 {} (t_walkstar st.subst t)
  ⇒
  type_e_determ (convert_menv menv) cenv tenv e`,
 rw [type_e_determ_def] >>
 (infer_e_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
 pop_assum mp_tac >>
 (infer_e_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
 rw [] >>
 `t_wfs init_infer_state.subst` by rw [t_wfs_def, init_infer_state_def] >>
 `t_wfs st.subst` by metis_tac [infer_e_wfs] >>
 first_x_assum (qspecl_then [`FEMPTY`, `menv`, `env`, `init_infer_state`, `[]`] mp_tac) >>
 first_x_assum (qspecl_then [`FEMPTY`, `menv`, `env`, `init_infer_state`, `[]`] mp_tac) >>
 rw [sub_completion_empty, init_infer_state_def] >>
 fs [sub_completion_def] >>
 imp_res_tac pure_add_constraints_success >>
 fs [t_compat_def] >>
 metis_tac [t_walkstar_no_vars]);

val generalise_complete_lem = Q.prove (
`∀n s t tvs s' t' tvs next_uvar.
  t_wfs s ∧ check_s 0 (count next_uvar) s ∧
  check_t 0 (count next_uvar) t ∧
  generalise 0 n FEMPTY (t_walkstar s t) = (tvs,s',t') ⇒
  ∃ec1 last_sub.
    t' = t_walkstar last_sub t ∧ t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub`,
 rw [] >>
 mp_tac (Q.SPECL [`n`, `s`, `[t]`] generalise_complete) >>
 rw [generalise_def, LET_THM]);

val type_e_determ_infer_e = Q.store_thm ("type_e_determ_infer_e",
`!menv cenv env tenv e st t.
  check_menv menv ∧
  check_cenv cenv ∧
  check_env {} env ∧
  num_tvs tenv = 0 ∧
  tenv_inv FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  type_e_determ (convert_menv menv) cenv tenv e
  ⇒
  check_t 0 {} (t_walkstar st.subst t)`,
 rw [type_e_determ_def] >>
 `t_wfs init_infer_state.subst` by rw [t_wfs_def, init_infer_state_def] >>
 `t_wfs st.subst` by metis_tac [infer_e_wfs] >>
 `check_t 0 (count st.next_uvar) t`
          by (imp_res_tac infer_e_check_t >>
              fs [init_infer_state_def]) >>
 `check_s 0 (count st.next_uvar) st.subst` 
           by (match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`menv`, `cenv`, `env`, `e`, `init_infer_state`] >>
               rw [init_infer_state_def, check_s_def]) >>
 `?l. set l = count st.next_uvar DIFF FDOM st.subst` 
          by metis_tac [FINITE_COUNT, FINITE_DIFF, SET_TO_LIST_INV] >>
 qabbrev_tac `inst1 = MAP (\n. (Infer_Tuvar n, Infer_Tbool)) l` >>
 qabbrev_tac `inst2 = MAP (\n. (Infer_Tuvar n, Infer_Tint)) l` >>
 (* Because we're instantiating exactly the unconstrained variables *)
 `?s1. sub_completion 0 st.next_uvar st.subst inst1 s1` by cheat >>
 `?s2. sub_completion 0 st.next_uvar st.subst inst2 s2` by cheat >>
 imp_res_tac sub_completion_wfs >>
 mp_tac (Q.SPECL [`menv`, `cenv`, `env`, `e`, `init_infer_state`, `st`, `tenv`, `t`, `inst1`, `s1`] (CONJUNCT1 infer_e_sound)) >>
 mp_tac (Q.SPECL [`menv`, `cenv`, `env`, `e`, `init_infer_state`, `st`, `tenv`, `t`, `inst2`, `s2`] (CONJUNCT1 infer_e_sound)) >>
 imp_res_tac tenv_inv_empty_to >>
 rw [init_infer_state_def] >>
 `convert_t (t_walkstar s1 t) = convert_t (t_walkstar s2 t)` by metis_tac [] >>
 CCONTR_TAC >>
 (* From here, we know that there is some unification variable in t_walkstar st.subst t, and that
  * it is therefore in FDOM s1 and FDOM s2 but not in FDOM st.subst. Hence it is in l, and thus
  * mapped to different types in inst1 and inst2. Thus, t_walkstar s1 t ≠ t_walkstar s2 t, a contradiction. *)
 cheat); 

val _ = export_theory ();

