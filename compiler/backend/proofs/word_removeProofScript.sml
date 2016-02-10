open preamble BasicProvers word_removeTheory wordSemTheory wordPropsTheory;

val _ = new_theory "word_removeProof";

(* Seq and MustTerminate are the hard cases and they're done *)
val word_remove_correct = store_thm("word_remove_correct",``
  ∀prog st res rst.
  evaluate(prog,st) = (res,rst) ∧
  res ≠ SOME Error ⇒
  ∃clk.
  evaluate(remove_must_terminate prog,st with <|clock:=st.clock+clk;termdep:=0|>) = (res,rst with termdep:=0)``,
  recInduct evaluate_ind>>
  fs[evaluate_def,remove_must_terminate_def,state_component_equality,call_env_def,get_var_def,set_var_def,dec_clock_def]>>rw[]
  >-
    (EVERY_CASE_TAC>>fs[]>>cheat)
  >- cheat
  >- cheat
  >- cheat
  >- (EVERY_CASE_TAC>>fs[state_component_equality])
  >- cheat
  >- cheat
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (qexists_tac`0`>>simp[state_component_equality])
  >- (*hard*)
    (qpat_assum`A=(res,rst)`mp_tac>>simp[]>>
    split_pair_tac>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    strip_tac>>fs[]>>
    rveq>>
    imp_res_tac evaluate_dec_clock>>fs[]>>
    imp_res_tac evaluate_add_clock>>fs[]>>
    last_x_assum(qspec_then`s.clock` assume_tac)>>
    metis_tac[])
  >-
    (qpat_assum`A=(res,rst)`mp_tac>>simp[]>>
    split_pair_tac>>fs[]>>
    IF_CASES_TAC>>fs[]>-
      (strip_tac>>fs[]>>
      imp_res_tac evaluate_add_clock>>
      rfs[]>>pop_assum kall_tac>>
      qexists_tac`clk+clk'`>>ntac 2 strip_tac>>
      pop_assum(qspec_then`clk'` assume_tac)>>fs[ADD_COMM]>>
      `s.clock + (clk+clk') = clk'+(clk+s.clock)` by simp[]>>
      fs[]>>rw[]>>
      simp[])
    >>
      rw[]>>fs[]>>
      qexists_tac`clk`>>fs[ADD_COMM])
  >- (EVERY_CASE_TAC>>fs[state_component_equality,fromList2_def])
  >- cheat
  >- cheat
  >- cheat
  >- cheat)

val _ = export_theory();
