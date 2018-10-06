(*
  Replaces calls to unknown functions with constant type errors.
*)
open preamble closLangTheory;

val _ = new_theory "clos_labels";
val _ = set_grammar_ancestry ["closLang","misc","sptree"];

val remove_dests_def = tDefine "remove_dests" `
  (remove_dests (ds:num_set) [] = []) /\
  (remove_dests ds ((x:closLang$exp)::y::xs) =
     HD (remove_dests ds [x]) :: remove_dests ds (y::xs)) /\
  (remove_dests ds [Var t v] = [Var t v]) /\
  (remove_dests ds [If t x1 x2 x3] =
     [If t (HD (remove_dests ds [x1]))
           (HD (remove_dests ds [x2]))
           (HD (remove_dests ds [x3]))]) /\
  (remove_dests ds [Let t xs x2] =
     let xs = remove_dests ds xs in
     let x2 = HD (remove_dests ds [x2]) in
       [Let t xs x2]) /\
  (remove_dests ds [Raise t x1] =
     [Raise t (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Handle t x1 x2] =
     [Handle t (HD (remove_dests ds [x1]))
              (HD (remove_dests ds [x2]))]) /\
  (remove_dests ds [Op t op xs] =
     [Op t op (remove_dests ds xs)]) /\
  (remove_dests ds [Tick t x] = [Tick t (HD (remove_dests ds [x]))]) /\
  (remove_dests ds [Call t ticks dest xs] =
   if IS_SOME (lookup dest ds) then
    [Call t ticks dest (remove_dests ds xs)]
   else [Op t (if NULL xs then (String"") else El) (remove_dests ds xs)]) /\
  (remove_dests ds [App t NONE x1 xs] =
  [App t NONE (HD (remove_dests ds [x1])) (remove_dests ds xs)]) /\
  (remove_dests ds [App t (SOME dest) x1 xs] =
  if IS_SOME (lookup dest ds) then
    [App t (SOME dest) (HD (remove_dests ds [x1])) (remove_dests ds xs)]
  else
    if NULL xs then [Op t El []]
    else [Op t (String"") (remove_dests ds xs ++ remove_dests ds [x1])]) /\
  (remove_dests ds [Letrec t loc_opt vs fns x1] =
     let m = LENGTH fns in
     let new_fns =
       MAP (\(num_args, x).
         (num_args, HD (remove_dests ds [x]))) fns in
     [Letrec t loc_opt vs new_fns (HD (remove_dests ds [x1]))]) /\
  (remove_dests ds [Fn t loc_opt vs num_args x1] =
    [Fn t loc_opt vs num_args (HD (remove_dests ds [x1]))])`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp []
   \\ rpt strip_tac
   \\ imp_res_tac exp1_size_lemma
   \\ simp []);

val compile_def = Define`
  compile prog =
    let dests = fromAList (MAP (λ(n,_,_). (n,())) prog) in
    MAP (λ(n,args,exp). (n, args, HD(remove_dests dests [exp]))) prog`;

val _ = export_theory();
