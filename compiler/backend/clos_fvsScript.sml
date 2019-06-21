(*
  Replaces free variables with constant type errors.
*)
open preamble closLangTheory;

val _ = new_theory "clos_fvs";
val _ = set_grammar_ancestry ["closLang"];

val remove_fvs_def = tDefine "remove_fvs" `
  (remove_fvs fvs [] = []) /\
  (remove_fvs fvs ((x:closLang$exp)::y::xs) =
     HD (remove_fvs fvs [x]) :: remove_fvs fvs (y::xs)) /\
  (remove_fvs fvs [Var t v] =
    if v < fvs then [Var t v]
    else [Op t El []]) /\
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
    [Fn t loc_opt vs num_args (HD (remove_fvs (num_args+fvs) [x1]))])`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp []
   \\ rpt strip_tac
   \\ imp_res_tac exp1_size_lemma
   \\ simp []);

val compile_def = Define`
  compile exps = remove_fvs 0 exps`;

Theorem LENGTH_remove_fvs:
   !fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs
Proof
  recInduct (fetch "-" "remove_fvs_ind") \\ simp [remove_fvs_def] \\ rw []
QED

val _ = export_theory();
