(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang", "backend_common"];


Definition load_shape_def:
  (load_shape One e = [Load e]) /\
  (load_shape (Comb shp) e = load_shapes shp e) /\
  (* merge the following to one, also add 'a' *)
  (load_shapes [] _ =  []) /\
  (load_shapes (sh::shs) e =
   load_shape sh e ++
   load_shapes shs (Op Add [e; Const (byte$bytes_in_word * n2w (size_of_shape sh))]))
End


val _ = export_theory();
