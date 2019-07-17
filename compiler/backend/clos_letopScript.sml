(*
  This simple compiler phase tidies up after function inlining, in
  particular it turns `Let [x0; x1; ...] (Op op [Var 0; Var 1; ...])`
  into `Op op [x0; x1; ...]`, which enables further optimisation
  later, e.g. in bvi_tailrec.
*)
open preamble closLangTheory;

val _ = new_theory "clos_letop";

val _ = set_grammar_ancestry ["closLang"]

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

val var_list_def = Define `
  (var_list n [] [] = T) /\
  (var_list n (Var t m :: xs) (y::ys) = ((m = n) /\ var_list (n+1) xs ys)) /\
  (var_list _ _ _ = F)`

val dest_op_def = Define `
  (dest_op (Op t op xs) args = (if var_list 0 xs args then SOME op else NONE)) /\
  (dest_op _ _ = NONE)`

val let_op_def = tDefine "let_op" `
  (let_op [] = []) /\
  (let_op ((x:closLang$exp)::y::xs) =
     HD (let_op [x]) :: let_op (y::xs)) /\
  (let_op [Var t v] = [Var t v]) /\
  (let_op [If t x1 x2 x3] =
     [If t (HD (let_op [x1]))
           (HD (let_op [x2]))
           (HD (let_op [x3]))]) /\
  (let_op [Let t xs x2] =
     let xs = let_op xs in
     let x2 = HD (let_op [x2]) in
       case dest_op x2 xs of
       | SOME op => [Op t op xs]
       | NONE => [Let t xs x2]) /\
  (let_op [Raise t x1] =
     [Raise t (HD (let_op [x1]))]) /\
  (let_op [Handle t x1 x2] =
     [Handle t (HD (let_op [x1]))
              (HD (let_op [x2]))]) /\
  (let_op [Op t op xs] =
     [Op t op (let_op xs)]) /\
  (let_op [Tick t x] = [Tick t (HD (let_op [x]))]) /\
  (let_op [Call t ticks dest xs] = [Call t ticks dest (let_op xs)]) /\
  (let_op [App t loc_opt x1 xs] = [App t loc_opt (HD (let_op [x1])) (let_op xs)]) /\
  (let_op [Letrec t loc_opt vs fns x1] =
     let new_fns = MAP (\(num_args, x). (num_args, HD (let_op [x]))) fns in
     [Letrec t loc_opt vs new_fns (HD (let_op [x1]))]) /\
  (let_op [Fn t loc_opt vs num_args x1] = [Fn t loc_opt vs num_args (HD (let_op [x1]))])`
  (WF_REL_TAC `measure exp3_size`
   \\ simp []
   \\ rpt strip_tac
   \\ imp_res_tac exp1_size_lemma
   \\ simp []);

val let_op_ind = theorem "let_op_ind";

Theorem LENGTH_let_op:
   !xs. LENGTH (let_op xs) = LENGTH xs
Proof
  recInduct let_op_ind \\ simp [let_op_def]
  \\ rw [] \\ CASE_TAC \\ simp []
QED

val _ = export_theory();
