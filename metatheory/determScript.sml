open preamble MiniMLTheory bigSmallEquivTheory;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀ cenv env e r1.
   evaluate cenv env e r1 ⇒
   ∀ r2. evaluate cenv env e r2 ⇒
   (r1 = r2)) ∧
 (∀ cenv env es r1.
   evaluate_list cenv env es r1 ⇒
   ∀ r2. evaluate_list cenv env es r2 ⇒
   (r1 = r2)) ∧
 (∀ cenv env v pes r1.
   evaluate_match cenv env v pes r1 ⇒
   ∀ r2. evaluate_match cenv env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);

val big_exp_determ' = Q.store_thm ("big_exp_determ'",
`(∀ env e r1.
   evaluate' env e r1 ⇒
   ∀ r2. evaluate' env e r2 ⇒
   (r1 = r2)) ∧
 (∀ env es r1.
   evaluate_list' env es r1 ⇒
   ∀ r2. evaluate_list' env es r2 ⇒
   (r1 = r2)) ∧
 (∀ env v pes r1.
   evaluate_match' env v pes r1 ⇒
   ∀ r2. evaluate_match' env v pes r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate'_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate'_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);

val big_determ = Q.store_thm ("big_determ",
`!cenv env ds r1.
  evaluate_decs cenv env ds r1 ⇒
  !r2.
    evaluate_decs cenv env ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_decs_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
metis_tac [big_exp_determ, result_11, result_distinct,
           match_result_11, match_result_distinct]);

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ = Q.store_thm ("small_exp_determ",
`!cenv env e r1 r2.
  small_eval cenv env e [] r1 ∧ small_eval cenv env e [] r2
  ⇒
  (r1 = r2)`,
metis_tac [big_exp_determ, small_big_exp_equiv]);

val small_determ = Q.store_thm ("small_determ",
`!cenv env ds r1 r2.
  d_small_eval cenv env ds NONE r1 ∧ d_small_eval cenv env ds NONE r2
  ⇒
  (r1 = r2)`,
metis_tac [big_determ, small_big_equiv]);

val _ = export_theory ();

