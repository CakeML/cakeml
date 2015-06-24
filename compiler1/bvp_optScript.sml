open preamble bvp_simpTheory bvp_liveTheory bvp_spaceTheory;

val _ = new_theory"bvp_opt";

(* combine bvp optimisations *)

val optimise_def = Define `
  optimise prog = bvp_space$compile (FST (bvp_live$compile (simp prog Skip) LN))`;

val _ = export_theory();
