(*
  A simple function-inlining optimisation within the BVL language.
  There is a more advanced inlining optimisation as part of
  clos_known.
*)
open preamble bvlTheory bvl_handleTheory;

val _ = new_theory "bvl_inline";

(* tick_inline -- a function that inlines a function body *)

Definition tick_inline_def:
  (tick_inline cs [] = []) /\
  (tick_inline cs (x::y::xs) =
     HD (tick_inline cs [x]) :: tick_inline cs (y::xs)) /\
  (tick_inline cs [Var v] = [Var v]) /\
  (tick_inline cs [If x1 x2 x3] =
     [If (HD (tick_inline cs [x1]))
         (HD (tick_inline cs [x2]))
         (HD (tick_inline cs [x3]))]) /\
  (tick_inline cs [Let xs x2] =
     [Let (tick_inline cs xs)
           (HD (tick_inline cs [x2]))]) /\
  (tick_inline cs [Raise x1] =
     [Raise (HD (tick_inline cs [x1]))]) /\
  (tick_inline cs [Handle x1 x2] =
     [Handle (HD (tick_inline cs [x1]))
             (HD (tick_inline cs [x2]))]) /\
  (tick_inline cs [Op op xs] =
     [Op op (tick_inline cs xs)]) /\
  (tick_inline cs [Tick x] =
     [Tick (HD (tick_inline cs [x]))]) /\
  (tick_inline cs [Force m n] = [Force m n]) /\
  (tick_inline cs [Call ticks dest xs] =
     case dest of NONE => [Call ticks dest (tick_inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call ticks dest (tick_inline cs xs)]
     | SOME (arity,code) => [Let (tick_inline cs xs) (mk_tick (SUC ticks) code)])
End

Definition tick_inline_sing_def:
  (tick_inline_sing cs (Var v) = Var v) /\
  (tick_inline_sing cs (If x1 x2 x3) =
     (If (tick_inline_sing cs x1)
         (tick_inline_sing cs x2)
         (tick_inline_sing cs x3))) /\
  (tick_inline_sing cs (Let xs x2) =
     (Let (tick_inline_list cs xs)
          (tick_inline_sing cs x2))) /\
  (tick_inline_sing cs (Raise x1) =
     (Raise (tick_inline_sing cs x1))) /\
  (tick_inline_sing cs (Handle x1 x2) =
     (Handle (tick_inline_sing cs x1)
             (tick_inline_sing cs x2))) /\
  (tick_inline_sing cs (Op op xs) =
     (Op op (tick_inline_list cs xs))) /\
  (tick_inline_sing cs (Tick x) =
     (Tick (tick_inline_sing cs x))) /\
  (tick_inline_sing cs (Force m n) = Force m n) /\
  (tick_inline_sing cs (Call ticks dest xs) =
     case dest of NONE => Call ticks dest (tick_inline_list cs xs) | SOME n =>
     case lookup n cs of
     | NONE => Call ticks dest (tick_inline_list cs xs)
     | SOME (arity,code) =>
         Let (tick_inline_list cs xs) (mk_tick (SUC ticks) code)) ∧
  (tick_inline_list cs [] = []) /\
  (tick_inline_list cs (x::xs) =
     (tick_inline_sing cs x) :: tick_inline_list cs xs)
End

Theorem tick_inline_sing:
  (∀e. tick_inline cs [e] = [tick_inline_sing cs e]) ∧
  (∀es. tick_inline_list cs es = tick_inline cs es)
Proof
  Induct \\ gvs [tick_inline_sing_def,tick_inline_def]
  \\ rw [] \\ every_case_tac
  \\ Cases_on ‘es’ \\ gvs [tick_inline_sing_def,tick_inline_def]
QED

(* This definition is written to exit as soon as possible. *)
Definition is_small_aux_def:
  (is_small_aux n [] = n) /\
  (is_small_aux n (x::y::xs) =
     if n = 0n then n else
       let n = is_small_aux n [x] in if n = 0 then n else
         is_small_aux n (y::xs)) /\
  (is_small_aux n [Var v] = n) /\
  (is_small_aux n [If x1 x2 x3] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n [x1] in if n = 0 then 0 else
     let n = is_small_aux n [x2] in if n = 0 then 0 else
       is_small_aux n [x3]) /\
  (is_small_aux n [Let xs x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n xs in if n = 0 then 0 else
       is_small_aux n [x2]) /\
  (is_small_aux n [Raise x1] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n [x1]) /\
  (is_small_aux n [Handle x1 x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n [x1] in if n = 0 then 0 else
       is_small_aux n [x2]) /\
  (is_small_aux n [Op op xs] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n xs) /\
  (is_small_aux n [Tick x] = is_small_aux n [x]) /\
  (is_small_aux n [Force _ _] = n) /\
  (is_small_aux n [Call ticks dest xs] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n xs)
End

Definition is_small_sing_def:
  (is_small_sing n (Var v) = n) /\
  (is_small_sing n (If x1 x2 x3) =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_sing n x1 in if n = 0 then 0 else
     let n = is_small_sing n x2 in if n = 0 then 0 else
       is_small_sing n x3) /\
  (is_small_sing n (Let xs x2) =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_list n xs in if n = 0 then 0 else
       is_small_sing n x2) /\
  (is_small_sing n (Raise x1) =
     let n = n - 1 in if n = 0 then 0 else
       is_small_sing n x1) /\
  (is_small_sing n (Handle x1 x2) =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_sing n x1 in if n = 0 then 0 else
       is_small_sing n x2) /\
  (is_small_sing n (Op op xs) =
     let n = n - 1 in if n = 0 then 0 else
       is_small_list n xs) /\
  (is_small_sing n (Tick x) = is_small_sing n x) /\
  (is_small_sing n (Force _ _) = n) /\
  (is_small_sing n (Call ticks dest xs) =
     let n = n - 1 in if n = 0 then 0 else
       is_small_list n xs) /\
  (is_small_list n [] = n) /\
  (is_small_list n (x::xs) =
     if n = 0n then n else
       let n = is_small_sing n x in if n = 0 then n else
         is_small_list n xs)
End

Theorem is_small_sing:
  (∀e n. is_small_aux n [e] = is_small_sing n e) ∧
  (∀es n. is_small_list n es = is_small_aux n es)
Proof
  Induct \\ gvs [is_small_sing_def,is_small_aux_def] \\ rw []
  \\ Cases_on ‘es’ \\ gvs [is_small_sing_def,is_small_aux_def]
  \\ qsuff_tac ‘(∀e. is_small_sing 0 e = 0) ∧
                (∀e. is_small_list 0 e = 0)’ \\ gvs []
  \\ Induct \\ gvs [is_small_sing_def]
QED

Definition is_small_def:
  is_small limit e = ~(is_small_aux limit [e] = 0)
End

Theorem is_small_eq = is_small_def |> SRULE [is_small_sing];

Definition is_rec_def:
  (is_rec n [] = F) /\
  (is_rec n (x::y::xs) =
     if is_rec n [x] then T else
       is_rec n (y::xs)) /\
  (is_rec n [Var v] = F) /\
  (is_rec n [If x1 x2 x3] =
     if is_rec n [x1] then T else
     if is_rec n [x2] then T else
       is_rec n [x3]) /\
  (is_rec n [Let xs x2] =
     if is_rec n xs then T else
       is_rec n [x2]) /\
  (is_rec n [Raise x1] = is_rec n [x1]) /\
  (is_rec n [Handle x1 x2] =
     if is_rec n [x1] then T else
       is_rec n [x2]) /\
  (is_rec n [Op op xs] = is_rec n xs) /\
  (is_rec n [Tick x] = is_rec n [x]) /\
  (is_rec n [Force _ _] = F) /\
  (is_rec n [Call ticks dest xs] =
     if dest = SOME n then T else is_rec n xs)
End

Definition is_rec_sing_def:
  (is_rec_sing n (Var v) = F) /\
  (is_rec_sing n (If x1 x2 x3) =
     if is_rec_sing n x1 then T else
     if is_rec_sing n x2 then T else
       is_rec_sing n x3) /\
  (is_rec_sing n (Let xs x2) =
     if is_rec_list n xs then T else
       is_rec_sing n x2) /\
  (is_rec_sing n (Raise x1) = is_rec_sing n x1) /\
  (is_rec_sing n (Handle x1 x2) =
     if is_rec_sing n x1 then T else
       is_rec_sing n x2) /\
  (is_rec_sing n (Op op xs) = is_rec_list n xs) /\
  (is_rec_sing n (Tick x) = is_rec_sing n x) /\
  (is_rec_sing n (Force _ _) = F) /\
  (is_rec_sing n (Call ticks dest xs) =
     if dest = SOME n then T else is_rec_list n xs) /\
  (is_rec_list n [] = F) /\
  (is_rec_list n (x::xs) =
     if is_rec_sing n x then T else
       is_rec_list n xs)
End

Theorem is_rec_sing:
  (∀e n. is_rec n [e] = is_rec_sing n e) ∧
  (∀es n. is_rec_list n es = is_rec n es)
Proof
  Induct \\ gvs [is_rec_sing_def,is_rec_def] \\ rw []
  \\ Cases_on ‘es’ \\ gvs [is_rec_sing_def,is_rec_def]
QED

Definition must_inline_def:
  must_inline name limit e =
    if is_small limit e then ~(is_rec name [e]) else F
End

Theorem must_inline_eq = must_inline_def |> SRULE [is_rec_sing];

Definition tick_inline_all_def:
  (tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
  (tick_inline_all limit cs ((n,arity:num,e1)::xs) aux =
     let e2 = HD (tick_inline cs [e1]) in
     let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
       tick_inline_all limit cs2 xs ((n,arity,e2)::aux))
End

Theorem tick_inline_all_eq =
  tick_inline_all_def |> SRULE [tick_inline_sing];

Definition tick_compile_prog_def:
  tick_compile_prog limit cs prog = tick_inline_all limit cs prog []
End

Theorem LENGTH_tick_inline:
   !cs xs. LENGTH (tick_inline cs xs) = LENGTH xs
Proof
  recInduct tick_inline_ind \\ REPEAT STRIP_TAC
  \\ fs [Once tick_inline_def,LET_DEF] \\ rw [] \\ every_case_tac \\ fs []
QED

Theorem HD_tick_inline[simp]:
   [HD (tick_inline cs [x])] = tick_inline cs [x]
Proof
  `LENGTH (tick_inline cs [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_tick_inline]
  \\ Cases_on `tick_inline cs [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC
QED

(* remove_ticks -- a function that removes Ticks *)

Definition remove_ticks_def:
  (remove_ticks [] = []) /\
  (remove_ticks (x::y::xs) =
     HD (remove_ticks [x]) :: remove_ticks (y::xs)) /\
  (remove_ticks [Var v] = [Var v]) /\
  (remove_ticks [If x1 x2 x3] =
     [If (HD (remove_ticks [x1]))
         (HD (remove_ticks [x2]))
         (HD (remove_ticks [x3]))]) /\
  (remove_ticks [Let xs x2] =
     [Let (remove_ticks xs) (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Raise x1] =
     [Raise (HD (remove_ticks [x1]))]) /\
  (remove_ticks [Handle x1 x2] =
     [Handle (HD (remove_ticks [x1]))
             (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Op op xs] =
     [Op op (remove_ticks xs)]) /\
  (remove_ticks [Tick x] = remove_ticks [x]) /\
  (remove_ticks [Force m n] = [Force m n]) /\
  (remove_ticks [Call ticks dest xs] =
     [Call 0 dest (remove_ticks xs)])
End

Definition remove_ticks_sing_def:
  (remove_ticks_sing (Var v) = Var v) /\
  (remove_ticks_sing (If x1 x2 x3) =
     If (remove_ticks_sing x1)
        (remove_ticks_sing x2)
        (remove_ticks_sing x3)) /\
  (remove_ticks_sing (Let xs x2) =
     Let (remove_ticks_list xs) (remove_ticks_sing x2)) /\
  (remove_ticks_sing (Raise x1) =
     Raise (remove_ticks_sing x1)) /\
  (remove_ticks_sing (Handle x1 x2) =
     Handle (remove_ticks_sing x1)
            (remove_ticks_sing x2)) /\
  (remove_ticks_sing (Op op xs) =
     Op op (remove_ticks_list xs)) /\
  (remove_ticks_sing (Tick x) = remove_ticks_sing x) /\
  (remove_ticks_sing (Force m n) = Force m n) /\
  (remove_ticks_sing (Call ticks dest xs) =
     Call 0 dest (remove_ticks_list xs)) /\
  (remove_ticks_list [] = []) /\
  (remove_ticks_list (x::xs) =
     (remove_ticks_sing x) :: remove_ticks_list xs)
End

Theorem remove_ticks_sing:
  (∀e. remove_ticks [e] = [remove_ticks_sing e]) ∧
  (∀es. remove_ticks_list es = remove_ticks es)
Proof
  Induct \\ gvs [remove_ticks_sing_def,remove_ticks_def] \\ rw []
  \\ Cases_on ‘es’ \\ gvs [remove_ticks_sing_def,remove_ticks_def]
QED

Theorem LENGTH_remove_ticks[simp]:
   !xs. LENGTH (remove_ticks xs) = LENGTH xs
Proof
  recInduct (theorem "remove_ticks_ind") \\ fs [remove_ticks_def]
QED

Theorem remove_ticks_SING[simp]:
   [HD (remove_ticks [r])] = remove_ticks [r]
Proof
  qsuff_tac `?a. remove_ticks [r] = [a]` \\ rw[] \\ fs []
  \\ `LENGTH (remove_ticks [r]) = LENGTH [r]` by fs [LENGTH_remove_ticks]
  \\ Cases_on `remove_ticks [r]` \\ fs []
QED

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

Definition var_list_def:
  var_list n [] [] = T /\
  var_list n (bvl$Var m :: xs) (y::ys) = (m = n /\ var_list (n+1) xs ys) /\
  var_list _ _ _ = F
End

Definition dest_op_def:
  dest_op (bvl$Op op xs) args = (if var_list 0 xs args then SOME op else NONE) /\
  dest_op _ _ = NONE
End

Definition let_op_def:
  (let_op [] = []) /\
  (let_op ((x:bvl$exp)::y::xs) =
     HD (let_op [x]) :: let_op (y::xs)) /\
  (let_op [Var v] = [Var v]) /\
  (let_op [If x1 x2 x3] =
     [If (HD (let_op [x1]))
         (HD (let_op [x2]))
         (HD (let_op [x3]))]) /\
  (let_op [Let xs x2] =
     let xs = let_op xs in
     let x2 = HD (let_op [x2]) in
       case dest_op x2 xs of
       | SOME op => [Op op xs]
       | NONE => [Let xs x2]) /\
  (let_op [Raise x1] =
     [Raise (HD (let_op [x1]))]) /\
  (let_op [Handle x1 x2] =
     [Handle (HD (let_op [x1]))
              (HD (let_op [x2]))]) /\
  (let_op [Op op xs] =
     [Op op (let_op xs)]) /\
  (let_op [Tick x] = [Tick (HD (let_op [x]))]) /\
  (let_op [Force m n] = [Force m n]) /\
  (let_op [Call ticks dest xs] = [Call ticks dest (let_op xs)])
End

Definition let_op_one_def:
  (let_op_one (Var v) = Var v) /\
  (let_op_one (If x1 x2 x3) =
     If (let_op_one x1)
        (let_op_one x2)
        (let_op_one x3)) /\
  (let_op_one (Let xs x2) =
     let xs = let_op_list xs in
     let x2 = let_op_one x2 in
       case dest_op x2 xs of
       | SOME op => Op op xs
       | NONE => Let xs x2) /\
  (let_op_one (Raise x1) =
     Raise (let_op_one x1)) /\
  (let_op_one (Handle x1 x2) =
     Handle (let_op_one x1)
            (let_op_one x2)) /\
  (let_op_one (Op op xs) =
     Op op (let_op_list xs)) /\
  (let_op_one (Tick x) = Tick (let_op_one x)) /\
  (let_op_one (Force m n) = Force m n) /\
  (let_op_one (Call ticks dest xs) = Call ticks dest (let_op_list xs)) /\
  (let_op_list [] = []) /\
  (let_op_list ((x:bvl$exp)::xs) =
     (let_op_one x) :: let_op_list xs)
End

Theorem let_op_one:
  (∀e. let_op [e] = [let_op_one e]) ∧
  (∀es. let_op_list es = let_op es)
Proof
  Induct \\ gvs [let_op_one_def,let_op_def] \\ rw []
  \\ every_case_tac \\ gvs []
  \\ Cases_on ‘es’ \\ gvs [let_op_one_def,let_op_def]
QED

Definition let_op_sing_def:
  let_op_sing x =
    case let_op [x] of
    | (y::ys) => y
    | _ => Op (IntOp (Const 0)) []
End

Theorem let_op_sing_eq = let_op_sing_def |> SRULE [let_op_one];

Definition optimise_def:
  optimise split_seq cut_size (name,arity, exp) =
    (name,arity,bvl_handle$compile_any split_seq cut_size arity
                  (let_op_sing (HD (remove_ticks [exp]))))
End

Theorem optimise_eq = optimise_def |> SRULE [remove_ticks_sing];

Definition compile_inc_def:
  compile_inc limit split_seq cut_size cs prog =
    let (cs,prog1) = tick_compile_prog limit cs prog in
      (cs, MAP (optimise split_seq cut_size) prog1)
End

Definition compile_prog_def:
  compile_prog limit split_seq cut_size prog =
    compile_inc limit split_seq cut_size LN prog
End

val _ = export_theory();
