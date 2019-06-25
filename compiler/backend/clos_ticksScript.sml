(*
  This simple compiler phase removes all Tick operations. Tick
  operations appear as a side effect of function inlining, and can be
  removed because they have no observable behaviour. It is good idea
  to remove them because they get in the way of pattern matching done
  by several optimisations.
*)
open preamble closLangTheory;

val _ = new_theory "clos_ticks";

val _ = set_grammar_ancestry ["closLang"]

val remove_ticks_def = tDefine "remove_ticks" `
  (remove_ticks [] = []) /\
  (remove_ticks ((x:closLang$exp)::y::xs) =
     HD (remove_ticks [x]) :: remove_ticks (y::xs)) /\
  (remove_ticks [Var t v] = [Var t v]) /\
  (remove_ticks [If t x1 x2 x3] =
     [If t (HD (remove_ticks [x1]))
           (HD (remove_ticks [x2]))
           (HD (remove_ticks [x3]))]) /\
  (remove_ticks [Let t xs x2] =
     [Let t (remove_ticks xs) (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Raise t x1] =
     [Raise t (HD (remove_ticks [x1]))]) /\
  (remove_ticks [Handle t x1 x2] =
     [Handle t (HD (remove_ticks [x1]))
               (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Op t op xs] =
     [Op t op (remove_ticks xs)]) /\
  (remove_ticks [Tick t x1] = remove_ticks [x1]) /\
  (remove_ticks [Call t ticks dest xs] =
     [Call t 0 dest (remove_ticks xs)]) /\
  (remove_ticks [App t loc_opt x1 xs] =
     [App t loc_opt (HD (remove_ticks [x1])) (remove_ticks xs)]) /\
  (remove_ticks [Letrec t loc_opt vs fns x1] =
     let new_fns = MAP (\(num_args, x). (num_args, HD (remove_ticks [x]))) fns in
     [Letrec t loc_opt vs new_fns (HD (remove_ticks [x1]))]) /\
  (remove_ticks [Fn t loc_opt vs num_args x1] =
     [Fn t loc_opt vs num_args (HD (remove_ticks [x1]))])`
 (WF_REL_TAC `measure exp3_size`
  \\ simp []
  \\ rpt strip_tac
  \\ imp_res_tac exp1_size_lemma
  \\ simp []);

val remove_ticks_ind = theorem "remove_ticks_ind";

Theorem LENGTH_remove_ticks:
   !(es:closLang$exp list). LENGTH (remove_ticks es) = LENGTH es
Proof
  recInduct remove_ticks_ind \\ fs [remove_ticks_def]
QED

val _ = export_theory();
