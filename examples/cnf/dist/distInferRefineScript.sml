(*
    Specification of distributed inference instantiated for ccnf
 *)
Theory distInferRefine
Ancestors
  finite_map list pred_set relation distInfer cnf ccnf
Libs
  bossLib

(* could go to satisfies_cnf *)

Definition sat_infer_def:
  sat_infer facts fact ⇔
  ∀w. satisfies_vcfml w facts ⇒ satisfies_vcclause w fact
End

Theorem cut_elimination_sat_infer:
  cut_elimination sat_infer
Proof
  rw[cut_elimination_def,sat_infer_def,
     satisfies_vcfml_def,
     satisfies_vcclause_def,
     satisfies_cclause_def,
     satisfies_fml_gen_def,
     SF DNF_ss
    ]
QED

Theorem assumption_sat_infer:
  assumption sat_infer
Proof
  rw[assumption_def,sat_infer_def,
     satisfies_vcfml_def,
     satisfies_vcclause_def,
     satisfies_cclause_def,
     satisfies_fml_gen_def,
     SF DNF_ss
    ]
QED

Theorem monotonic_sat_infer:
  monotonic sat_infer
Proof
  rw[monotonic_def,sat_infer_def,
     satisfies_vcfml_def,
     satisfies_vcclause_def,
     satisfies_cclause_def,
     satisfies_fml_gen_def,
     SF DNF_ss
    ]
QED

Theorem sat_step_sound:
  (reduce sat_infer)꙳ st st' ∧
  (∀name facts. FLOOKUP st.procs name = SOME(SOME facts) ⇒ FRANGE facts ⊆ oprems) ∧
  set st.facts ⊆ oprems ∧
  st.validated = ∅ ∧
  fact ∈ st'.validated
  ⇒
  sat_infer oprems fact
Proof
  metis_tac[step_sound,monotonic_sat_infer,assumption_sat_infer,
            cut_elimination_sat_infer]
QED
