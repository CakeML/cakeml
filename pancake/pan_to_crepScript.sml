(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang","backend_common"];


Datatype:
  compexp = Node ((num # compexp) list)
          | Leaf (('a crepLang$exp) list)
End

Datatype:
  context =
    <| var_nums  : panLang$varname |-> num list
     ; lab_num   : panLang$funname |-> num |>
End

Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) = SOME (Leaf [Const c])) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME ns => SOME (Leaf (MAP Var ns))
   | NONE => NONE) /\
  (compile_exp ctxt (Label fname) =
   case FLOOKUP ctxt.lab_num fname of
   | SOME n => SOME (Leaf [Label n])
   | NONE => NONE) /\
  (compile_exp ctxt (Struct []) =
   SOME (Node [])) /\
  (compile_exp ctxt (Struct es) =
   case (OPT_MMAP (compile_exp ctxt) es) of
   | SOME cexps => SOME (Node (MAPi $, cexps))
   | NONE => NONE) /\
  (compile_exp ctxt (Field index e) =
   case (compile_exp ctxt e) of
   | SOME (Node cexpi) =>
     if index < LENGTH cexpi then SOME (EL index (MAP SND cexpi))
     else NONE
   | _ => NONE) /\
  (compile_exp ctxt (Load sh e) = ARB) /\
  (compile_exp ctxt (LoadByte e) =
   case (compile_exp ctxt e) of
   | SOME (Leaf [Const c]) => SOME (Leaf [LoadByte (Const c)])
   | SOME (Leaf [Var v]) => SOME (Leaf [LoadByte (Var v)])
   | SOME (Leaf [LoadByte e]) => SOME (Leaf [LoadByte (LoadByte e)])
     (* also op, cmp and shift, what about Load? no label? *)
   | _ => NONE) /\
  (compile_exp ctxt (Op ops es) = ARB) /\
  (* all es should be should be evaluated to leafs of single set
    with either Const, Var Load, see cmp and shift later? no label? *)
  (compile_exp ctxt (Cmp c e e') = ARB) /\
  (compile_exp ctxt (Shift sh e n) = ARB)
Termination
  cheat
End


(*
for assign:
Pancake:                              Crepe:
  Assign v (* shape *) (Word e)       Assign vn (Word e)
  Assign v (Label lab)                Assign vn (Label e)
  Assign v (* shape *) (Struct ws)   Sequence_of_assignments vs (compile_exps)

for store:
  compile: One (* can be label or word *)  (* compile source , if one then only one memory write,
                                              otherwise list of memory writes *)
  store bytes might be easy

(* do we compile expressions separately? to some extend
compiling expressions separately does not make sense *)

Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog _ (Dec v e p) = ARB) /\
  (compile_prog _ (Assign v e) = ARB)
End
*)



(*

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
*)
val _ = export_theory();
