(*
  TODO: placeholder for clos_lift pass
*)
open preamble closLangTheory;

val _ = new_theory"clos_lift";
val _ = set_grammar_ancestry ["closLang"]

Definition compile_def:
  compile (n:num) (exps:exp list) = (ARB:num,ARB:exp list)
End

Definition lift_compile_inc_def:
  lift_compile_inc (n:num) (p:clos_prog) = (ARB:num,ARB:clos_prog)
End

val _ = export_theory()
