open preamble bvlTheory clos_to_bvlTheory;

val _ = new_theory "bvl_const";

(*

   This is a BVL transformation that propagates simple and
   cheap-to-compute context-free expression from Let bindings. It also
   performs some simple constant folding with SmartOp (below).

   The most significant impact of this optimisation is that it removes
   each Var in a Let, i.e. Let [...; Var ...; ...] ..., and replaces
   them with constants Let [...; Op (Const _) []; ...] .... and
   replaces all occurrences of the bound var with a lookup to the
   original variable.

   bvi_let is a simpler version of this optimisation.

*)

val isConst_def = Define `
  (isConst (Op (Const _) []) = T) /\
  (isConst _ = F)`;
val _ = export_rewrites["isConst_def"];

val getConst_def = Define `
  (getConst (Op (Const i) []) = i) /\
  (getConst _ = 0)`;
val _ = export_rewrites["getConst_def"];

val dest_Op_Const_def = Define `
  (dest_Op_Const ((Op (Const i) xs):bvl$exp) =
    if NULL xs then SOME i else NONE) /\
  (dest_Op_Const _ = NONE)`;

val is_simple_def = Define `
  (is_simple ((Op (Cons _) xs):bvl$exp) = NULL xs) /\
  (is_simple (Op (Const _) xs) = NULL xs) /\
  (is_simple _ = F)`;

val SmartOp_def = Define `
  SmartOp op (xs:bvl$exp list) =
    let default = Op op xs in
    if LENGTH xs <> 2 then default else
    if MEM op [Add; Sub; Mult; Div; Mod; Less; LessEq; Greater; GreaterEq] then
      let ys = MAP dest_Op_Const xs in
        (if IS_SOME (EL 0 ys) /\ IS_SOME (EL 1 ys) then
           let x1 = THE (EL 1 ys) in
           let x2 = THE (EL 0 ys) in
           (case op of
            | Add => Op (Const (x1 + x2)) []
            | Sub => Op (Const (x1 - x2)) []
            | Mult => Op (Const (x1 * x2)) []
            | Div => if x2 = 0 then default else Op (Const (x1 / x2)) []
            | Mod => if x2 = 0 then default else Op (Const (x1 % x2)) []
            | Less => Bool (x1 < x2)
            | LessEq => Bool (x1 <= x2)
            | Greater => Bool (x1 > x2)
            | GreaterEq => Bool (x1 >= x2)
            | _ => default)
         else default)
    else if op = Equal /\ is_simple (EL 0 xs) /\ is_simple (EL 1 xs) then
      Bool (EL 0 xs = EL 1 xs)
    else default`

val extract_def = Define `
  (extract ((Var n):bvl$exp) ys = SOME ((Var (n + LENGTH ys + 1)):bvl$exp)) /\
  (extract (Op (Const i) xs) ys = SOME (Op (Const i) [])) /\
  (extract (Op (Cons t) xs) ys =
    if NULL xs then SOME (Op (Cons t) []) else NONE) /\
  (extract _ _ = NONE)`

val extract_list_def = Define `
  (extract_list [] = []) /\
  (extract_list (x::xs) = extract x xs :: extract_list xs)`

val delete_var_def = Define `
  (delete_var ((Var n):bvl$exp) = Op (Const 0) []) /\
  (delete_var x = x)`;

val compile_def = tDefine "compile" `
  (compile env [] = []) /\
  (compile env (x::y::xs) = compile env [x] ++ compile env (y::xs)) /\
  (compile env [Var v] =
     case LLOOKUP env v of
     | NONE => [Var v]
     | SOME NONE => [Var v]
     | SOME (SOME (Var i)) => [Var (v + i)]
     | SOME (SOME x) => [x]) /\
  (compile env [If x1 x2 x3] =
     let y1 = HD (compile env [x1]) in
     let y2 = HD (compile env [x2]) in
     let y3 = HD (compile env [x3]) in
       if y1 = Bool T then [y2] else
       if y1 = Bool F then [y3] else
         [If y1 y2 y3]) /\
  (compile env [Let xs x2] =
     let ys = compile env xs in
       [Let (MAP delete_var ys)
            (HD (compile (extract_list ys ++ env) [x2]))]) /\
  (compile env [Handle x1 x2] =
     [Handle (HD (compile env [x1])) (HD (compile (NONE::env) [x2]))]) /\
  (compile env [Raise x1] =
     [Raise (HD (compile env [x1]))]) /\
  (compile env [Op op xs] = [SmartOp op (compile env xs)]) /\
  (compile env [Tick x] = [Tick (HD (compile env [x]))]) /\
  (compile env [Call t dest xs] = [Call t dest (compile env xs)])`
 (WF_REL_TAC `measure (exp1_size o SND)`);

val compile_ind = theorem"compile_ind";

val compile_length = Q.store_thm("compile_length[simp]",
  `!n xs. LENGTH (compile n xs) = LENGTH xs`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [compile_def,ADD1,LET_DEF]
  \\ every_case_tac \\ SRW_TAC [] [] \\ DECIDE_TAC);

val compile_HD_SING = store_thm("compile_HD_SING",
  ``[HD (compile n [x])] = compile n [x]``,
  MP_TAC (Q.SPECL [`n`,`[x]`] compile_length)
  \\ Cases_on `compile n [x]` \\ fs [LENGTH_NIL]);

val compile_exp_def = Define `
  compile_exp x = case compile [] [x] of (y::_) => y | _ => Var 0 (* impossible *)`;

val _ = export_theory();
