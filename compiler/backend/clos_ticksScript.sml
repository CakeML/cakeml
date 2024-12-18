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

Definition remove_ticks_def:
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
     [Fn t loc_opt vs num_args (HD (remove_ticks [x1]))])
Termination
  WF_REL_TAC `measure exp3_size`
  \\ simp []
  \\ rpt strip_tac
  \\ imp_res_tac exp1_size_lemma
  \\ simp []
End

Definition remove_ticks_sing_def:
  (remove_ticks_sing (Var t v) = (Var t v)) /\
  (remove_ticks_sing (If t x1 x2 x3) =
     (If t ( (remove_ticks_sing (x1)))
           ( (remove_ticks_sing (x2)))
           ( (remove_ticks_sing (x3))))) /\
  (remove_ticks_sing (Let t xs x2) =
     (Let t (remove_ticks_list xs) ( (remove_ticks_sing (x2))))) /\
  (remove_ticks_sing (Raise t x1) =
     (Raise t ( (remove_ticks_sing (x1))))) /\
  (remove_ticks_sing (Handle t x1 x2) =
     (Handle t ( (remove_ticks_sing (x1)))
               ( (remove_ticks_sing (x2))))) /\
  (remove_ticks_sing (Op t op xs) =
     (Op t op (remove_ticks_list xs))) /\
  (remove_ticks_sing (Tick t x1) = remove_ticks_sing (x1)) /\
  (remove_ticks_sing (Call t ticks dest xs) =
     (Call t 0 dest (remove_ticks_list xs))) /\
  (remove_ticks_sing (App t loc_opt x1 xs) =
     (App t loc_opt ( (remove_ticks_sing (x1))) (remove_ticks_list xs))) /\
  (remove_ticks_sing (Letrec t loc_opt vs fns x1) =
     let new_fns = remove_ticks_let fns in
     (Letrec t loc_opt vs new_fns ( (remove_ticks_sing (x1))))) /\
  (remove_ticks_sing (Fn t loc_opt vs num_args x1) =
     (Fn t loc_opt vs num_args ( (remove_ticks_sing (x1))))) ∧
  (remove_ticks_list [] = []) /\
  (remove_ticks_list ((x:closLang$exp)::xs) =
     remove_ticks_sing x :: remove_ticks_list xs) ∧
  (remove_ticks_let [] = []) /\
  (remove_ticks_let ((num_args, x)::xs) =
   (num_args, remove_ticks_sing x) :: remove_ticks_let xs)
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL x => exp_size x
                            | INR(INL x) => exp3_size x
                            | INR(INR x) => exp1_size x’
End

val remove_ticks_ind = theorem "remove_ticks_ind";

Theorem LENGTH_remove_ticks:
   !(es:closLang$exp list). LENGTH (remove_ticks es) = LENGTH es
Proof
  recInduct remove_ticks_ind \\ fs [remove_ticks_def]
QED

Theorem remove_ticks_sing_eq:
  (∀e. remove_ticks [e] = [remove_ticks_sing e]) ∧
  (∀es. remove_ticks es = remove_ticks_list es) ∧
  (∀fns.
    remove_ticks_let fns =
    MAP (λ(num_args, x). (num_args, HD (remove_ticks [x]))) fns
  )
Proof
  ho_match_mp_tac remove_ticks_sing_ind >>
  reverse $ rw[remove_ticks_def, remove_ticks_sing_def] >>
  Cases_on `es` >> gvs[remove_ticks_def, remove_ticks_sing_def]
QED

Definition compile_inc_def:
  compile_inc (e, xs) = (remove_ticks e, [])
End

val _ = export_theory();
