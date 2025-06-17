(*
  Replaces free variables with constant type errors.
*)
open preamble closLangTheory;

val _ = new_theory "clos_fvs";
val _ = set_grammar_ancestry ["closLang"];

Definition remove_fvs_def:
  (remove_fvs fvs [] = []) /\
  (remove_fvs fvs ((x:closLang$exp)::y::xs) =
     HD (remove_fvs fvs [x]) :: remove_fvs fvs (y::xs)) /\
  (remove_fvs fvs [Var t v] =
    if v < fvs then [Var t v]
    else [Op t (MemOp El) []]) /\
  (remove_fvs fvs [If t x1 x2 x3] =
     [If t (HD (remove_fvs fvs [x1]))
           (HD (remove_fvs fvs [x2]))
           (HD (remove_fvs fvs [x3]))]) /\
  (remove_fvs fvs [Let t xs x2] =
     let xs = remove_fvs fvs xs in
     let n = LENGTH xs in
     let x2 = HD (remove_fvs (fvs+n) [x2]) in
       [Let t xs x2]) /\
  (remove_fvs fvs [Raise t x1] =
     [Raise t (HD (remove_fvs fvs [x1]))]) /\
  (remove_fvs fvs [Handle t x1 x2] =
     [Handle t (HD (remove_fvs fvs [x1]))
              (HD (remove_fvs (fvs+1) [x2]))]) /\
  (remove_fvs fvs [Op t op xs] =
     [Op t op (remove_fvs fvs xs)]) /\
  (remove_fvs fvs [Tick t x] = [Tick t (HD (remove_fvs fvs [x]))]) /\
  (remove_fvs fvs [Call t ticks dest xs] = [Call t ticks dest (remove_fvs fvs xs)]) /\
  (remove_fvs fvs [App t loc_opt x1 xs] = [App t loc_opt (HD (remove_fvs fvs [x1])) (remove_fvs fvs xs)]) /\
  (remove_fvs fvs [Letrec t loc_opt vs fns x1] =
     let m = LENGTH fns in
     let new_fvs = case vs of NONE => fvs | SOME x => LENGTH x in
     let new_fns =
       MAP (\(num_args, x).
         (num_args, HD (remove_fvs (num_args+m+new_fvs) [x]))) fns in
     [Letrec t loc_opt vs new_fns (HD (remove_fvs (m + fvs) [x1]))]) /\
  (remove_fvs fvs [Fn t loc_opt vs num_args x1] =
    let fvs = case vs of NONE => fvs | SOME x => LENGTH x in
    [Fn t loc_opt vs num_args (HD (remove_fvs (num_args+fvs) [x1]))])
End

Definition remove_fvs_sing_def:
  (remove_fvs_sing fvs (Var t v) =
    if v < fvs then Var t v
    else Op t (MemOp El) []) /\
  (remove_fvs_sing fvs (If t x1 x2 x3) =
     If t (remove_fvs_sing fvs x1)
          (remove_fvs_sing fvs x2)
          (remove_fvs_sing fvs x3)) /\
  (remove_fvs_sing fvs (Let t xs x2) =
     let xs = remove_fvs_list fvs xs in
     let n = LENGTH xs in
     let x2 = remove_fvs_sing (fvs+n) x2 in
       Let t xs x2) /\
  (remove_fvs_sing fvs (Raise t x1) =
     Raise t (remove_fvs_sing fvs x1)) /\
  (remove_fvs_sing fvs (Handle t x1 x2) =
     Handle t (remove_fvs_sing fvs x1)
              (remove_fvs_sing (fvs+1) x2)) /\
  (remove_fvs_sing fvs (Op t op xs) =
     Op t op (remove_fvs_list fvs xs)) /\
  (remove_fvs_sing fvs (Tick t x) = Tick t (remove_fvs_sing fvs x)) /\
  (remove_fvs_sing fvs (Call t ticks dest xs) =
    Call t ticks dest (remove_fvs_list fvs xs)) /\
  (remove_fvs_sing fvs (App t loc_opt x1 xs) =
    App t loc_opt (remove_fvs_sing fvs x1) (remove_fvs_list fvs xs)) /\
  (remove_fvs_sing fvs (Letrec t loc_opt vs fns x1) =
     let m = LENGTH fns in
     let new_fvs = case vs of NONE => fvs | SOME x => LENGTH x in
     let new_fns = remove_fvs_let m new_fvs fns in
     Letrec t loc_opt vs new_fns (remove_fvs_sing (m + fvs) x1)) /\
  (remove_fvs_sing fvs (Fn t loc_opt vs num_args x1) =
    let fvs = case vs of NONE => fvs | SOME x => LENGTH x in
    Fn t loc_opt vs num_args (remove_fvs_sing (num_args+fvs) x1)) ∧
  (remove_fvs_list fvs [] = []) /\
  (remove_fvs_list fvs ((x:closLang$exp)::xs) =
     remove_fvs_sing fvs x :: remove_fvs_list fvs xs) ∧
  (remove_fvs_let m fvs [] = []) /\
  (remove_fvs_let m new_fvs ((num_args,x)::xs) =
     (num_args, remove_fvs_sing (num_args+m+new_fvs) x)::remove_fvs_let m new_fvs xs)
Termination
  WF_REL_TAC `measure $ λx. case x of INL (_,e) => exp_size e
                                    | INR(INL (_,es)) => list_size exp_size es
                                    | INR(INR (_,_,es)) => list_size (pair_size (λx. x) exp_size) es`
End

Theorem remove_fvs_sing_eq:
  (∀fvs e. remove_fvs fvs [e] = [remove_fvs_sing fvs e]) ∧
  (∀fvs es. remove_fvs fvs es = remove_fvs_list fvs es) ∧
  (∀m new_fvs fns.
    remove_fvs_let m new_fvs fns =
    MAP (λ(num_args, x). (num_args, HD (remove_fvs (num_args+m+new_fvs) [x]))) fns
  )
Proof
  ho_match_mp_tac remove_fvs_sing_ind >>
  reverse $ rw[remove_fvs_def, remove_fvs_sing_def] >>
  Cases_on `es` >> gvs[remove_fvs_def, remove_fvs_sing_def]
QED

Definition compile_def:
  compile exps = remove_fvs 0 exps
End

Theorem compile_eq:
  compile exps = remove_fvs_list 0 exps
Proof
  simp[compile_def, remove_fvs_sing_eq]
QED

Definition compile_inc_def:
  compile_inc (e, xs) = (compile e, [])
End

Theorem LENGTH_remove_fvs:
   !fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs
Proof
  recInduct (fetch "-" "remove_fvs_ind") \\ simp [remove_fvs_def] \\ rw []
QED

val _ = export_theory();
