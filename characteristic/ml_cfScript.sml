open HolKernel Parse boolLib bossLib preamble;
open set_sepTheory;

val _ = new_theory "ml_cf";

(*
STAR_def
bigStepTheory.evaluate_rules
bigStepTheory.evaluate_ind
*)

val _ = type_abbrev("v_map",``:num |-> v``)

val fmap2set_def = Define `
  fmap2set (f:'a |-> 'b) = fun2set ((\a. f ' a), FDOM f)`

(*
  ``(one (2n, Litv (IntLit 5)) * anything) (fmap2set (s:v_map))``
*)

val cf_def = Define `
  (cf (Lit l) P Q <=> \(s:v_map). P s /\ Q (Litv l) s) /\
  (cf _ _ _ <=> \s. F)`;

val _ = export_theory();
