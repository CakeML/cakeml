(*
  Translation of the to_data compiler function.
*)
open preamble cv_transLib cv_stdTheory;
open backendTheory backend_asmTheory;

val _ = new_theory "to_data_cv";

val _ = cv_memLib.use_long_names := true;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;
val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans miscTheory.list_max_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

Theorem to_data_fake:
  backend_asm$to_data c p = (c,[],LN)
Proof
  cheat
QED

val _ = cv_trans to_data_fake;

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
