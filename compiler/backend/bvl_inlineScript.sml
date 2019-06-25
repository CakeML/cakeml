(*
  A simple function-inlining optimisation within the BVL language.
  There is a more advanced inlining optimisation as part of
  clos_known.
*)
open preamble bvlTheory bvl_handleTheory;

val _ = new_theory "bvl_inline";

(* tick_inline -- a function that inlines a function body *)

val tick_inline_def = tDefine "tick_inline" `
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
  (tick_inline cs [Call ticks dest xs] =
     case dest of NONE => [Call ticks dest (tick_inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call ticks dest (tick_inline cs xs)]
     | SOME (arity,code) => [Let (tick_inline cs xs) (mk_tick (SUC ticks) code)])`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val tick_inline_ind = theorem"tick_inline_ind";

(* This definition is written to exit as soon as possible. *)
val is_small_aux_def = tDefine "is_small_aux" `
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
  (is_small_aux n [Call ticks dest xs] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val is_small_def = Define `
  is_small limit e = ~(is_small_aux limit [e] = 0)`;

val is_rec_def = tDefine "is_rec" `
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
  (is_rec n [Call ticks dest xs] =
     if dest = SOME n then T else is_rec n xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val must_inline_def = Define `
  must_inline name limit e =
    if is_small limit e then ~(is_rec name [e]) else F`

val tick_inline_all_def = Define `
  (tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
  (tick_inline_all limit cs ((n,arity:num,e1)::xs) aux =
     let e2 = HD (tick_inline cs [e1]) in
     let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
       tick_inline_all limit cs2 xs ((n,arity,e2)::aux))`;

val tick_compile_prog_def = Define `
  tick_compile_prog limit cs prog = tick_inline_all limit cs prog []`

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

val remove_ticks_def = tDefine "remove_ticks" `
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
  (remove_ticks [Call ticks dest xs] =
     [Call 0 dest (remove_ticks xs)])`
  (WF_REL_TAC `measure exp1_size`);

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

val var_list_def = Define `
  var_list n [] [] = T /\
  var_list n (bvl$Var m :: xs) (y::ys) = (m = n /\ var_list (n+1) xs ys) /\
  var_list _ _ _ = F`

val dest_op_def = Define `
  dest_op (bvl$Op op xs) args = (if var_list 0 xs args then SOME op else NONE) /\
  dest_op _ _ = NONE`

val let_op_def = tDefine "let_op" `
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
  (let_op [Call ticks dest xs] = [Call ticks dest (let_op xs)])`
  (WF_REL_TAC `measure exp1_size`);

val let_op_sing_def = Define `
  let_op_sing x =
    case let_op [x] of
    | (y::ys) => y
    | _ => Op (Const 0) []`;

val optimise_def = Define `
  optimise split_seq cut_size (name,arity, exp) =
    (name,arity,bvl_handle$compile_any split_seq cut_size arity
                  (let_op_sing (HD (remove_ticks [exp]))))`;

val compile_inc_def = Define `
  compile_inc limit split_seq cut_size cs prog =
    let (cs,prog1) = tick_compile_prog limit cs prog in
      (cs, MAP (optimise split_seq cut_size) prog1)`

val compile_prog_def = Define `
  compile_prog limit split_seq cut_size prog =
    compile_inc limit split_seq cut_size LN prog`

val _ = export_theory();
