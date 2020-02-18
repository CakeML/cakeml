(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang","backend_common"];


Definition shape_size_def:
  (shape_size [] = 0:num) /\
  (shape_size (One::shapes) = 1 + shape_size shapes) /\
  (shape_size (Comb shape::shapes) =
     shape_size shape + shape_size shapes)
Termination
  cheat
End

Definition shape_tags_def:
  (shape_tags [] sname (tag:num) = []) /\
  (shape_tags (One::shapes) sname tag =
   (sname,tag) :: shape_tags shapes sname (tag + 1)) /\
  (shape_tags (Comb shape::shapes) sname tag =
   shape_tags shape sname tag ++ shape_tags shapes sname (tag + shape_size shape))
Termination
  cheat
End


Definition compile_struct_def:
  (compile_struct One sname tag = [(sname,tag)]) /\
  (compile_struct (Comb shapes) sname tag = shape_tags shapes sname tag)
End


Definition compile_exp_def:
  (compile_exp (Const c) = [Const c]) /\
  (compile_exp ctxt (* Var -> shape # varname list *) (Var vname) = case lookup vname ctxt of SOME (sh,vs) => (sh, MAP Var vs) |
               NONE => (One, []) (* should not happen *)   ) /\
  (compile_exp (Label fname) = [Label fname]) /\


  (compile_exp (Struct exps) = Comb something, ) /\


  (compile_exp (Lookup sname shape index) = ARB) /\
  (* first we should flat sname using shape, and then we should pick the member corresponding to the
  index, that could be a list *)
  (compile_exp (Load e shape) = ARB) /\
  (compile_exp (LoadByte e) = [LoadByte e]) /\
  (compile_exp (Op bop es) = [Op bop es]) /\
  (compile_exp (Cmp cmp e e') = [Cmp cmp e e']) /\
  (compile_exp (Shift shift e n) = [Shift shift e n])
End


Definition compile_def:
  compile (p:'a panLang$prog list) = (ARB:'a crepLang$prog list)
End

val _ = export_theory();
