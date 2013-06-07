open preamble SemanticPrimitivesTheory BigStepTheory bigSmallEquivTheory bigClockTheory;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
   ∀r2. evaluate ck menv cenv s env e r2 ⇒
   (r1 = r2)) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
   ∀r2. evaluate_list ck menv cenv s env es r2 ⇒
   (r1 = r2)) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
   ∀r2. evaluate_match ck menv cenv s env v pes r2 ⇒
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

val dec_determ = Q.store_thm ("dec_determ",
`!mn menv (cenv : envC) s env d r1.
  evaluate_dec mn menv cenv s env d r1 ⇒
  !r2.
    evaluate_dec mn menv (cenv : envC) s env d r2
    ⇒
    (r1 = r2)`,
rw [evaluate_dec_cases] >>
metis_tac [big_exp_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

val decs_determ = Q.store_thm ("decs_determ",
`!mn menv (cenv : envC) s env ds r1.
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
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

val prog_determ = Q.store_thm ("prog_determ",
`!menv (cenv : envC) s env ds r1.
  evaluate_prog menv cenv s env ds r1 ⇒
  !r2.
    evaluate_prog menv cenv s env ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_prog_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_prog_cases]) >>
fs [] >>
rw [] >>
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11,
           decs_determ]);

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ = Q.store_thm ("small_exp_determ",
`!menv cenv s env e r1 r2.
  small_eval menv cenv s env e [] r1 ∧ small_eval menv cenv s env e [] r2
  ⇒
  (r1 = r2)`,
rw [] >>
PairCases_on `r1` >>
PairCases_on `r2` >>
metis_tac [big_exp_determ, small_big_exp_equiv, PAIR_EQ]);

val _ = export_theory ();
