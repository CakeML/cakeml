open preamble bvlTheory ;

val _ = new_theory "bvl_inline";

(* A function that inlines a function body *)

val inline_def = tDefine "inline" `
  (inline cs [] = []) /\
  (inline cs (x::y::xs) =
     HD (inline cs [x]) :: inline cs (y::xs)) /\
  (inline cs [Var v] = [Var v]) /\
  (inline cs [If x1 x2 x3] =
     [If (HD (inline cs [x1]))
         (HD (inline cs [x2]))
         (HD (inline cs [x3]))]) /\
  (inline cs [Let xs x2] =
     [Let (inline cs xs)
           (HD (inline cs [x2]))]) /\
  (inline cs [Raise x1] =
     [Raise (HD (inline cs [x1]))]) /\
  (inline cs [Handle x1 x2] =
     [Handle (HD (inline cs [x1]))
              (HD (inline cs [x2]))]) /\
  (inline cs [Op op xs] =
     [Op op (inline cs xs)]) /\
  (inline cs [Tick x] = inline cs [x]) /\
  (inline cs [Call ticks dest xs] =
     case dest of NONE => [Call 0 dest (inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call 0 dest (inline cs xs)]
     | SOME (arity,code) => [Let (inline cs xs) code])`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val inline_ind = theorem"inline_ind";

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

val must_inline_def = Define `
  must_inline name limit e =
    if is_small limit e then ~(is_rec name [e]) else F`

val inline_all_def = Define `
  (inline_all limit cs [] aux = (cs,REVERSE aux)) /\
  (inline_all limit cs ((n,arity,e1)::xs) aux =
     let e2 = HD (inline cs [e1]) in
     let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
       inline_all limit cs2 xs ((n,arity,let_op_sing e2)::aux))`;

val compile_def = Define `
  compile limit cs prog = inline_all limit cs prog []`;

val compile_prog_def = Define `
  compile_prog limit prog =
    (* TODO: use compile from above in backendScript.sml *)
    SND (inline_all limit LN prog [])`

val LENGTH_inline = Q.store_thm("LENGTH_inline",
  `!cs xs. LENGTH (inline cs xs) = LENGTH xs`,
  recInduct inline_ind \\ REPEAT STRIP_TAC
  \\ fs [Once inline_def,LET_DEF] \\ rw [] \\ every_case_tac \\ fs []);

val HD_inline = Q.store_thm("HD_inline[simp]",
  `[HD (inline cs [x])] = inline cs [x]`,
  `LENGTH (inline cs [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_inline]
  \\ Cases_on `inline cs [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

val _ = export_theory();
