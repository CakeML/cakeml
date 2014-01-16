open preamble semanticPrimitivesTheory bigStepTheory bigSmallEquivTheory bigClockTheory;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

(* big_exp_determ moved to bigClockScript.sml *)

val dec_determ = Q.store_thm ("dec_determ",
`!mn s env d r1.
  evaluate_dec mn env s d r1 ⇒
  !r2.
    evaluate_dec mn env s d r2
    ⇒
    (r1 = r2)`,
rw [evaluate_dec_cases] >>
metis_tac [big_exp_determ, result_11,
result_distinct,PAIR_EQ,NOT_EXISTS,NOT_EVERY, match_result_11, match_result_distinct, optionTheory.SOME_11]);

val decs_determ = Q.store_thm ("decs_determ",
`!mn env s ds r1.
  evaluate_decs mn env s ds r1 ⇒
  !r2.
    evaluate_decs mn env s ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_decs_cases]) >>
fs [] >>
rw [] >>
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

val top_determ = Q.store_thm ("top_determ",
`!env s top r1.
  evaluate_top env s top r1 ⇒
  !r2.
    evaluate_top env s top r2
    ⇒
    (r1 = r2)`,
rw [evaluate_top_cases] >>
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11,
           decs_determ]);

val prog_determ = Q.store_thm ("prog_determ",
`!env s ds r1.
  evaluate_prog env s ds r1 ⇒
  !r2.
    evaluate_prog env s ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_prog_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_prog_cases]) >>
fs [] >>
rw [] >>
metis_tac [top_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ = Q.store_thm ("small_exp_determ",
`!env s e r1 r2.
  small_eval env s e [] r1 ∧ small_eval env s e [] r2
  ⇒
  (r1 = r2)`,
rw [] >>
PairCases_on `r1` >>
PairCases_on `r2` >>
metis_tac [big_exp_determ, small_big_exp_equiv, PAIR_EQ]);

val _ = export_theory ();
