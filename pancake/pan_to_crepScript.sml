(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang", "backend_common"];

(* i would be size_of_shape *)

(*
Definition load_shape_def:
  load_shape a i e =
    if i = (0:num) then []
    else if a = 0w then (Load e) :: load_shape (a + byte$bytes_in_word) (i-1) e
    else (Load (Op Add [e; Const a])) :: load_shape (a + byte$bytes_in_word) (i-1) e
End
*)

Definition load_shape_def:
  (load_shape a 0 e = []) ∧
  (load_shape a (SUC i) e =
     if a = 0w then (Load e) :: load_shape (a + byte$bytes_in_word) i e
     else (Load (Op Add [e; Const a])) :: load_shape (a + byte$bytes_in_word) i e)
End

val _ = export_theory();
