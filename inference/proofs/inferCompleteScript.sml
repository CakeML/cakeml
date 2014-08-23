open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open libPropsTheory astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;

val _ = new_theory "inferComplete";


(* Move to unification theory *)

val unify_fresh_uvar = Q.store_thm ("unify_fresh_uvar",
`!s uv t.
  t_wfs s ∧
  uv ∉ FDOM s
  ⇒
  (t_walk s t ≠ Infer_Tuvar uv ⇒ t_unify s (Infer_Tuvar uv) t = SOME (s |+ (uv, t_walk s t))) ∧
  (t_walk s t = Infer_Tuvar uv ⇒ t_unify s (Infer_Tuvar uv) t = SOME s)`,
 rw [t_unify_eqn, t_walk_eqn] >>
 `t_vwalk s uv = Infer_Tuvar uv` by rw [Once t_vwalk_eqn, FLOOKUP_DEF] >>
 rw [] >>
 Cases_on `t_walk s t` >>
 rw [t_ext_s_check_eqn, oc_tvar_db] >>
 cheat);

(* End unification stuff *)

val unconvert_t_def = tDefine "unconvert_t" `
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc)`
(wf_rel_tac `measure t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
    lookup_tenv x 0 tenv = SOME (tvs, t)
    ⇒
    check_freevars tvs [] t ∧
    ?t'. unconvert_t t = t_walkstar s t' ∧ lookup x env = SOME (tvs,t'))`;

    (*
val pure_add_constraints_exists = Q.prove (
`!ts s next_uvar s'.
  t_wfs s ∧
  sub_completion 0 next_uvar s [] s' ∧
  ⇒
  ?s'.
    pure_add_constraints s
      (ZIP (MAP (λn. Infer_Tuvar (next_uvar + n)) (COUNT_LIST (LENGTH ts)), ts)) 
      s'`,

 induct_on `ts` >>
 rw [COUNT_LIST_def, pure_add_constraints_def] >>
 fs [sub_completion_def, pure_add_constraints_def] >>
 rw [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = (SUC x) + y``] >>
 rw [Once SWAP_EXISTS_THM] >>
 FIRST_X_ASSUM (qspecl_then 

 rw [t_unify_eqn], t_walk_eqn, Once t_vwalk_eqn]
 every_case_tac >>
 rw []

val new_uvars_sub_completion_exists = Q.prove (
`!s constraints s' ts next_uvar.
  t_wfs s ∧
  EVERY (check_t 0 (count next_uvar)) ts ∧
  check_s 0 (count next_uvar) s ∧
  sub_completion 0 next_uvar s constraints s'
  ⇒
  ∃s''.
    sub_completion 0 (next_uvar + LENGTH ts) s
      (constraints++ZIP
         (MAP (λn. Infer_Tuvar (next_uvar + n))
            (COUNT_LIST (LENGTH ts)),ts)) s''`,

 rw [sub_completion_def, pure_add_constraints_append] >>
 rw [PULL_EXISTS] >>
 rw [Once SWAP_EXISTS_THM] >>
 qexists_tac `s'` >>
 rw []


 induct_on `constraints` >>
 rw [] >>
 >- (


 fs [sub_completion_def] >>
 PairCases_on `h` >>
 fs [pure_add_constraints_def] >>
 FIRST_X_ASSUM match_mp_tac >>
 qexists_tac `s'` >>
 rw [] >>
 metis_tac [{{{{{{{{{{{, t_unify_check_s]);



 rw [ZIP_COUNT_LIST, LENGTH_COUNT_LIST]


val infer_e_complete = Q.prove (

`(!tenvM tenvC tenvE e t. 
   type_e tenvM tenvC tenvE e t
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     tenv_inv s tenv tenvE
     ⇒
     ?t' st' s' constraints'.
       infer_e menv tenvC tenv e st = (Success t', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       t = convert_t (t_walkstar s' t')) ∧
 (!tenvM tenvC tenvE es ts. 
   type_es tenvM tenvC tenvE es ts
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     tenv_inv s tenv tenvE
     ⇒
     ?ts' st' s' constraints'.
       infer_es menv tenvC tenv es st = (Success ts', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       ts = MAP (convert_t o t_walkstar s') t') ∧
 (!tenvM tenvC tenvE funs env. 
   type_funs tenvM tenvC tenvE funs env
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     tenv_inv s tenv tenvE
     ⇒
     ?env' st' s' constraints'.
       infer_funs menv tenvC tenv funs st = (Success env', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       MAP SND env = MAP (convert_t o t_walkstar s') env')`,

 ho_match_mp_tac type_e_ind >>
 rw [success_eqns, infer_e_def]
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s'` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- cheat
 >- cheat
 >- cheat
 >- cheat

 >- (Cases_on `n` >>
     rw [success_eqns, infer_e_def] >>
     fs [t_lookup_var_id_def, tenv_inv_def]
     >- (res_tac >>
         rw [success_eqns] >>
         rw [Once SWAP_EXISTS_THM] >>
         qexists_tac `ZIP (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH targs)),
                           MAP unconvert_t targs)` >>
         `?constraints' s'. 
           sub_completion 0 (st.next_uvar + LENGTH targs) st.subst constraints' s' ∧
           check_t (LENGTH targs) (FDOM s') t'`
                  by cheat >>
         qexists_tac `s'` >>
         qexists_tac `constraints'` >>
         rw [] >>
         `t_wfs s'` by metis_tac [sub_completion_wfs] >>
         `count (st.next_uvar + LENGTH targs) ⊆ FDOM s'` by fs [sub_completion_def] >>
         `∀uv. uv ∈ FDOM s' ⇒ check_t 0 ∅ (t_walkstar s' (Infer_Tuvar uv))`
                 by (fs [sub_completion_def] >>
                     metis_tac []) >>
         imp_res_tac db_subst_infer_subst_swap >>
         rw [MAP_MAP_o, combinTheory.o_DEF] >>
         cheat)
     >- cheat)
 >- (`tenv_inv (bind n (0,Infer_Tuvar st.next_uvar) tenv) (bind_tenv n 0 t1 tenvE)`
              by (rw [bind_def, tenv_inv_def, bind_tenv_def] >>
                  cheat) >>
     `convert_menv menv = convert_menv menv` by cheat

     res_tac >>
     fs []
     rw []

     *)
val _ = export_theory ();
