(*
  This simple compiler phase tidies up after function inlining, in
  particular it turns `Let [x0; x1; ...] (Op op [Var 0; Var 1; ...])`
  into `Op op [x0; x1; ...]`, which enables further optimisation
  later, e.g. in bvi_tailrec.
*)
Theory clos_letop
Ancestors
  closLang
Libs
  preamble

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

Definition var_list_def:
  (var_list n [] [] = T) /\
  (var_list n (Var t m :: xs) (y::ys) = ((m = n) /\ var_list (n+1) xs ys)) /\
  (var_list _ _ _ = F)
End

Definition dest_op_def:
  (dest_op (Op t op xs) args = (if var_list 0 xs args then SOME op else NONE)) /\
  (dest_op _ _ = NONE)
End

Definition let_op_def:
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
  (let_op [Fn t loc_opt vs num_args x1] = [Fn t loc_opt vs num_args (HD (let_op [x1]))])
End

val let_op_ind = theorem "let_op_ind";

Theorem LENGTH_let_op:
   !xs. LENGTH (let_op xs) = LENGTH xs
Proof
  recInduct let_op_ind \\ simp [let_op_def]
  \\ rw [] \\ CASE_TAC \\ simp []
QED

Definition let_op_sing_def:
  (let_op_sing (Var t v) = (Var t v)) /\
  (let_op_sing (If t x1 x2 x3) =
     (If t ( (let_op_sing (x1)))
           ( (let_op_sing (x2)))
           ( (let_op_sing (x3))))) /\
  (let_op_sing (Let t xs x2) =
     let xs = let_op_list xs in
     let x2 =  (let_op_sing (x2)) in
       case dest_op x2 xs of
       | SOME op => (Op t op xs)
       | NONE => (Let t xs x2)) /\
  (let_op_sing (Raise t x1) =
     (Raise t ( (let_op_sing (x1))))) /\
  (let_op_sing (Handle t x1 x2) =
     (Handle t ( (let_op_sing (x1)))
              ( (let_op_sing (x2))))) /\
  (let_op_sing (Op t op xs) =
     (Op t op (let_op_list xs))) /\
  (let_op_sing (Tick t x) = (Tick t ( (let_op_sing (x))))) /\
  (let_op_sing (Call t ticks dest xs) = (Call t ticks dest (let_op_list xs))) /\
  (let_op_sing (App t loc_opt x1 xs) = (App t loc_opt ( (let_op_sing (x1))) (let_op_list xs))) /\
  (let_op_sing (Letrec t loc_opt vs fns x1) =
     let new_fns = let_op_let fns in
     (Letrec t loc_opt vs new_fns ( (let_op_sing (x1))))) /\
  (let_op_sing (Fn t loc_opt vs num_args x1) = (Fn t loc_opt vs num_args ( (let_op_sing (x1))))) ∧
  (let_op_list [] = []) /\
  (let_op_list ((x:closLang$exp)::xs) =
   let_op_sing x :: let_op_list xs) ∧
  (let_op_let [] = []) /\
  (let_op_let ((num_args,x:closLang$exp)::xs) =
   (num_args, let_op_sing x) :: let_op_let xs)
Termination
  wf_rel_tac ‘measure $ λx. case x of
                            | INL x => exp_size x
                            | INR(INL x) => list_size exp_size x
                            | INR(INR x) => list_size (pair_size (λx. x) exp_size) x’
End

Theorem let_op_sing_eq:
  (∀e. let_op [e] = [let_op_sing e]) ∧
  (∀es. let_op es = let_op_list es) ∧
  (∀fns.
    let_op_let fns =
    MAP (λ(num_args, x). (num_args, HD (let_op [x]))) fns
  )
Proof
  ho_match_mp_tac let_op_sing_ind >>
  reverse $ rw[let_op_def, let_op_sing_def]
  >- (Cases_on `es` >> gvs[let_op_def, let_op_sing_def]) >>
  rpt(PURE_TOP_CASE_TAC >> gvs[])
QED

Definition compile_inc_def:
  compile_inc (e, xs) = (let_op e, [])
End

