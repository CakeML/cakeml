(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang","backend_common"];

Datatype:
  context =
    <| var_nums : panLang$varname |-> shape # num list|>
End

(*
(* may be not needed right now *)
Definition load_with_shape_def:
  load_with_shape One e = ([Load e], One) /\
  load_with_shape (Comb []) e =  ([Const 0w], One) /\
  load_with_shape (Comb shape:shapes) e =
End
*)

Definition cexp_list_def:
  (cexp_list [] _ = []) /\
  (cexp_list _ [] = []) /\
  (cexp_list (One::sh) (e::es) = [e] :: cexp_list sh es) /\
  (cexp_list (Comb sh::sh') es =
   let  es' = FLAT (cexp_list sh es) in
   es' :: cexp_list sh' (DROP (LENGTH es') es))
Termination
  cheat
End

(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es)  of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End


Definition cexp_heads_simp_def:
  cexp_heads_simp es =
  if (MEM [] es) then NONE
  else SOME (MAP HD es)
End


Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

(*
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   if (MEM [] cexps) then ([Const 0w], One)
   else ([Op bop (MAP HD cexps)], One)) /\
*)


Definition load_shape_def:
  (load_shape One e = [Load e]) /\
  (load_shape (Comb shp) e = load_shapes shp e) /\

  (load_shapes [] _ =  []) /\
  (load_shapes (sh::shs) e =
   load_shape sh e ++ load_shapes shs (Op Add [e; Const byte$bytes_in_word]))
End



Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) =
   ([(Const c): 'a crepLang$exp], One)) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME (shape, []) => ([Const 0w], One) (* TOREVIEW : to avoid MAP [] *)
   | SOME (shape, ns) => (MAP Var ns, shape)
   | NONE => ([Const 0w], One)) /\
  (compile_exp ctxt (Label fname) = ([Label fname], One)) /\
  (compile_exp ctxt (Struct es) =
   let cexps = MAP (compile_exp ctxt) es in
   (* TODISC: should we do the empty check here as well? *)
   (FLAT (MAP FST cexps), Comb (MAP SND cexps))) /\
  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes =>
     if index < LENGTH shapes then
      (EL index (cexp_list shapes cexp), EL index shapes)
      else ([Const 0w], One)) /\
  (compile_exp ctxt (Load sh e) =
   let (cexp, sh) = compile_exp ctxt e in
   case cexp of
   | [] => ([Const 0w], One)
   | e::es => (load_shape sh e, sh)) /\ (* TODISC: what shape should we emit? *)
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | [] => ([Const 0w], One)
   | e::es => ([LoadByte e], One)) /\
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in (* TOREVIEW : to avoid MAP [] *)
   case cexp_heads exp of
   | NONE => ([Const 0w], One)
   | SOME es => ([Op bop es], One)) /\
  (compile_exp ctxt (Cmp cmp e e') =
   let ce  = FST (compile_exp ctxt e);
       ce' = FST (compile_exp ctxt e') in
   case (ce, ce') of
   | (e::es, e'::es') => ([Cmp cmp e e'], One)
   | (_, _) => ([Const 0w], One)) /\
 (compile_exp ctxt (Shift sh e n) =
   case FST (compile_exp ctxt e) of
   | [] => ([Const 0w], One)
   | e::es => ([Shift sh e n], One))
Termination
  cheat
End


(* assoc? *)
Definition list_seq_def:
  (list_seq [] = (Skip:'a crepLang$prog)) /\
  (list_seq [e] = e) /\
  (list_seq (e::e'::es) = Seq e (list_seq (e::es)))
End


Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog _ (Dec v e p) = ARB) /\
  (compile_prog _ (Assign v e) =
   if compile_exp e  --> SOME (leaf es) then (lookup v in var_nums --> vnums)
   then seq_list Seq (MAP2 Assign vnums es)) /\
  (compile_prog _ (Store dst src) =
       compile dest, compile src, then list of stores, what about addresses, aligned etc )
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

Definition compile_def:
  compile (p:'a panLang$prog list) = (ARB:'a crepLang$prog list)
End
*)
*)



val _ = export_theory();
