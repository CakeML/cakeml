open preamble bvlTheory clos_to_bvlTheory;

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
  (inline cs [Tick x] =
     [Tick (HD (inline cs [x]))]) /\
  (inline cs [Call ticks dest xs] =
     case dest of NONE => [Call ticks dest (inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call ticks dest (inline cs xs)]
     | SOME (arity,code) => [Let (inline cs xs) (mk_tick (SUC ticks) code)])`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val inline_ind = theorem"inline_ind";

(* This definition is written to exit as soon as possible. *)
val is_small_aux_def = tDefine "is_small_aux" `
  (is_small_aux n [] = n) /\
  (is_small_aux n (x::y::xs) =
     if n = 0 then n else
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

val inline_all_def = Define `
  (inline_all limit cs [] aux = REVERSE aux) /\
  (inline_all limit cs ((n,arity,e1)::xs) aux =
     let e2 = HD (inline cs [e1]) in
     let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
       inline_all limit cs2 xs ((n,arity,e2)::aux))`;

val compile_prog_def = Define `
  compile_prog limit prog =
    if limit = 0 then prog else inline_all limit LN prog []`

val LENGTH_inline = store_thm("LENGTH_inline",
  ``!cs xs. LENGTH (inline cs xs) = LENGTH xs``,
  recInduct inline_ind \\ REPEAT STRIP_TAC
  \\ fs [Once inline_def,LET_DEF] \\ rw [] \\ every_case_tac \\ fs []);

val HD_inline = store_thm("HD_inline[simp]",
  ``[HD (inline cs [x])] = inline cs [x]``,
  `LENGTH (inline cs [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_inline]
  \\ Cases_on `inline cs [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

val _ = export_theory();
