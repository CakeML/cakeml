open preamble MiniMLTheory bigSmallEquivTheory;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀menv (cenv : envC) s env e r1.
   evaluate menv cenv s env e r1 ⇒
   ∀r2. evaluate menv cenv s env e r2 ⇒
   (r1 = r2)) ∧
 (∀menv (cenv : envC) s env es r1.
   evaluate_list menv cenv s env es r1 ⇒
   ∀r2. evaluate_list menv cenv s env es r2 ⇒
   (r1 = r2)) ∧
 (∀menv (cenv : envC) s env v pes r1.
   evaluate_match menv cenv s env v pes r1 ⇒
   ∀r2. evaluate_match menv cenv s env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
res_tac >>
fs [] >>
rw [] >> 
metis_tac []);

(*
val big_exp_determ' = Q.store_thm ("big_exp_determ'",
`(∀s env e r1.
   evaluate' s env e r1 ⇒
   ∀r2. evaluate' s env e r2 ⇒
   (r1 = r2)) ∧
 (∀s env es r1.
   evaluate_list' s env es r1 ⇒
   ∀r2. evaluate_list' s env es r2 ⇒
   (r1 = r2)) ∧
 (∀s env v pes r1.
   evaluate_match' s env v pes r1 ⇒
   ∀r2. evaluate_match' s env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate'_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate'_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
res_tac >>
fs [] >>
rw [] >>
metis_tac []);
*)

val big_determ = Q.store_thm ("big_determ",
`!mn menv cenv s env ds r1.
  evaluate_decs mn menv cenv s env ds r1 ⇒
  !r2.
    evaluate_decs mn menv cenv s env ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_decs_cases]) >>
fs [] >>
rw [] >>
fs [evaluate_dec_cases] >>
rw [] >>
fs [] >>
rw [] >>
metis_tac [big_exp_determ, small_big_exp_equiv, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ = Q.store_thm ("small_exp_determ",
`!menv cenv s env e r1 r2.
  small_eval menv cenv s env e [] r1 ∧ small_eval menv cenv s env e [] r2
  ⇒
  (r1 = r2)`,
metis_tac [big_exp_determ, small_big_exp_equiv]);

val _ = export_theory ();

