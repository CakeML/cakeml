open preamble bviTheory
open backend_commonTheory;

(* Errors from dummy cases:

   Var 65534                  id_from_op 
   Call 23583 NONE [] NONE    comp
   Call 35505 NONE [] NONE    setup_call
   Var 65536                  push_call
   Var 65537                  mk_tailcall

   TODO At some point we can redo the code to
        place the accumulator argument /last/
        and get rid of some GENLIST stuff. There
        is no point in having it first.
*)

val _ = new_theory "bvi_tailrec";

val args_from_def = Define `
  (args_from (bvi$Call t (SOME d) as hdl) = SOME (t, d, as, hdl)) ∧
  (args_from _                            = NONE)
  `;

val is_arithmetic_def = Define `
  is_arithmetic Add       = T ∧
  is_arithmetic Mult      = T ∧
  is_arithmetic Sub       = T ∧
  is_arithmetic Div       = T ∧
  is_arithmetic Mod       = T ∧
  is_arithmetic (Const _) = T ∧
  is_arithmetic _         = F
  `;

val _ = Datatype `
  ok_arith_op = Plus | Times
  `;

val _ = Datatype `
  assoc_op = IntOp ok_arith_op
           | FunOp num num
  `;

val from_op_def = Define `
  (from_op Add  = IntOp Plus) ∧
  (from_op Mult = IntOp Times) ∧
  (from_op _    = FunOp 0 0)
  `

val to_op_def = Define `
  (to_op Plus  = Add) ∧
  (to_op Times = Mult)
  `;

val op_eq_def = Define `
  (op_eq (IntOp Plus)  (Op Add _)             ⇔ T) ∧
  (op_eq (IntOp Times) (Op Mult _)            ⇔ T) ∧
  (op_eq (FunOp n1 _)  (Call _ (SOME n2) _ _) ⇔ n1 = n2) ∧
  (op_eq _             _                      ⇔ F)
  `;

val apply_op_def = Define `
  (apply_op (IntOp op)  e1 e2 = Op (to_op op) [e1; e2]) ∧
  (apply_op (FunOp t n) e1 e2 = Call t (SOME n) [e1; e2] NONE)
  `;

val id_from_op_def = Define `
  (id_from_op (IntOp Plus)  = bvi$Op (Const 0) []) ∧
  (id_from_op (IntOp Times) = bvi$Op (Const 1) []) ∧
  (id_from_op _             = bvi$Var 65534) (* dummy *)
  `;

val op_binargs_def = Define `
  op_binargs (bvi$Op _ [e1; e2]) = SOME (e1, e2) ∧
  op_binargs _                   = NONE
  `;

val MEM_exp_size_imp = Q.store_thm ("MEM_exp_size_imp",
  `∀xs a. MEM a xs ⇒ bvi$exp_size a < exp2_size xs`,
  Induct \\ rw [bviTheory.exp_size_def] \\ res_tac \\ fs []);

val pure_op_def = closLangTheory.pure_op_def;

val is_pure_def = tDefine "is_pure" `
  (is_pure (Var _)       ⇔ T) ∧
  (is_pure (If x1 x2 x3) ⇔ is_pure x1 ∧ is_pure x2 ∧ is_pure x3) ∧
  (is_pure (Op op xs)    ⇔ EVERY is_pure xs ∧ pure_op op) ∧
  (is_pure (Let xs x1)   ⇔ EVERY is_pure xs ∧ is_pure x1) ∧
  (is_pure _             ⇔ F)`
  (WF_REL_TAC `measure exp_size` \\ rw []
  \\ imp_res_tac MEM_exp_size_imp \\ fs []);

val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ NONE) ⇔ d = SOME name) ∧
  (is_rec _    _                     ⇔ F)
  `;

val ok_tail_type_def = Define `
  (ok_tail_type name (Op op _)             ⇔ is_arithmetic op) ∧
  (ok_tail_type name (Let _ x1)            ⇔ ok_tail_type name x1) ∧
  (ok_tail_type name (Tick x1)             ⇔ ok_tail_type name x1) ∧
  (ok_tail_type name (If _ x2 x3)          ⇔
    ok_tail_type name x2 ∧ ok_tail_type name x3) ∧
  (ok_tail_type name _                     ⇔ F)
  `;

val binop_has_rec_def = Define `
  binop_has_rec name op exp ⇔
    (is_rec name exp) ∨ 
    (op_eq op exp ∧ 
    (case op_binargs exp of
    | NONE => F
    | SOME (x1, x2) => is_rec name x1))
  `;

val exp_size_op_binargs = Q.store_thm ("exp_size_op_binargs",
  `∀x x1 x2.
     op_binargs x = SOME (x1, x2) ⇒
       exp_size x1 < exp_size x ∧
       exp_size x2 < exp_size x`,

  Induct \\ fs [op_binargs_def]
  \\ ntac 3 strip_tac
  \\ Cases_on `l` \\ simp [op_binargs_def]
  \\ Cases_on `t` \\ simp [op_binargs_def]
  \\ Cases_on `t'` \\ simp [op_binargs_def]
  \\ fs [bviTheory.exp_size_def]);

(* somewhat wrong apparently, call gets nested inside extra op *)
val assoc_swap_def = Define `
  assoc_swap op from into =
    case op_binargs into of
    | NONE => apply_op op into from
    | SOME (x1, x2) => apply_op op x1 (apply_op op from x2)
  `;

val op_rewrite_def = tDefine "op_rewrite" `
  op_rewrite op name exp =
    if ¬op_eq op exp then
      (F, exp)
    else
      case op_binargs exp of 
      | NONE => (F, exp)
      | SOME (x1, x2) => 
        let (r1, y1) = op_rewrite op name x1 in
        let (r2, y2) = op_rewrite op name x2 in
          case (binop_has_rec name op y1, binop_has_rec name op y2) of
          | (F, F) => (F, exp)
          (*| (T, T) => (T, assoc_swap op y1 y2)*)
          | (T, T) => (F, exp)
          | (T, F) => if is_pure y2 then (T, assoc_swap op y2 y1) else (F, exp)
          | (F, T) => if is_pure y1 then (T, assoc_swap op y1 y2) else (F, exp)
  `
  (WF_REL_TAC `measure (exp_size o SND o SND)`
  \\ rpt strip_tac
  \\ drule exp_size_op_binargs
  \\ fs []);

val tail_check_def = Define `
  (tail_check name (Var _)        = NONE) ∧
  (tail_check name (Let _ x1)     = tail_check name x1) ∧
  (tail_check name (Tick x1)      = tail_check name x1) ∧
  (tail_check name (Raise x1)     = NONE) ∧
  (tail_check name (If _ x2 x3)   =
    case tail_check name x2 of
    | SOME op => SOME op
    | _       => tail_check name x3) ∧
  (tail_check name (Call _ _ _ _) = NONE) ∧
  (tail_check name (Op op xs)     =
    if op = Add ∨ op = Mult then
      let iop = from_op op in
        (case op_rewrite iop name (Op op xs) of
        | (T, _) => SOME iop
        | _ => NONE)
    else NONE)`;

val push_call_def = Define `
  (push_call n op acc exp (SOME (ticks, dest, args, handler)) =
    Call ticks (SOME n) (apply_op op exp (Var acc) :: args) handler) ∧
  (push_call _ _ _ _ _ = Var 65536) (* dummy *)
  `;

val mk_tailcall_def = Define `
  mk_tailcall n op name acc exp = 
    case op_rewrite op name exp of
    | (F, exp2) => apply_op op exp2 (Var acc)
    | (T, exp2) => 
        (case op_binargs exp2 of
        | NONE => Var 65537 (* dummy *)
        | SOME (call, exp3) => 
          push_call n op acc exp3 (args_from call))
  `;

val tail_rewrite_def = Define `
  (tail_rewrite n op name acc (Let xs x1) =
    Let xs (tail_rewrite n op name (acc + LENGTH xs) x1)) ∧
  (tail_rewrite n op name acc (Tick x1) =
    Tick (tail_rewrite n op name acc x1)) ∧
  (tail_rewrite n op name acc (Raise x1) = Raise x1) ∧
  (tail_rewrite n op name acc (If x1 x2 x3) =
    let y2 = tail_rewrite n op name acc x2 in
    let y3 = tail_rewrite n op name acc x3 in
      If x1 y2 y3) ∧
  (tail_rewrite n op name acc exp = mk_tailcall n op name acc exp)
  `;

val optimize_check_def = Define `
  optimize_check name exp =
    if ¬ok_tail_type name exp then
      NONE
    else
      tail_check name exp
  `;

val let_wrap_def = Define `
  let_wrap num_args exp =
    Let (GENLIST (λi. Var (i + 1)) num_args) exp
  `;

val mk_aux_call_def = Define `
  mk_aux_call name num_args id =
    Call 0 (SOME name) (id :: GENLIST (λi. Var (i + 0)) num_args) NONE
  `;

(* Instead of creating a wrapper which calls the transformed function
   (thus consuming a clock tick) we simply wrap the transformed expression
   in `let acc = id_from_op op in <transformed_expression>`.

   This way we get rid of clock ticks. Moreover, this type of auxiliary 'copy'
   can probably be removed somehow later -- or proven equivalent to the old
   type of auxiliary?  *)
val optimize_single_def = Define `
  optimize_single n name num_args exp =
    case optimize_check name exp of
    | NONE => NONE
    | SOME op =>
        let trw = tail_rewrite n op name num_args exp in
        let opt = let_wrap num_args trw in
        let aux = Let [id_from_op op] opt in
          SOME (aux, opt)
  `;

val optimize_prog_def = Define `
  (optimize_prog n [] = []) ∧
  (optimize_prog n ((nm, args, exp)::xs) =
    case optimize_single n nm args exp of
    | NONE => (nm, args, exp)::optimize_prog n xs
    | SOME (exp_aux, exp_opt) =>
        (nm, args, exp_aux)::(n, args + 1, exp_opt)::optimize_prog (n + 2) xs)
  `;

(* -- Evaluation tests. ----------------------------------------------------*)

(*
  length xxs =
    if xxs = [] then
      0
    else
      let
        xs = tl xxs
      in
        1 + length xs

  should optimize to SOME (...)
*)
val length1_fun_def = Define `
  length1_fun =
      If (Op Equal [Var 0; Op (Cons nil_tag) []])
         (Op (Const 0) [])
         (Let [Call 5 (SOME 1) [Var 0] NONE]
              (Op Add [Op (Const 1) []; Call 10 (SOME 2) [Var 0] NONE]))
  `;

(*
  length acc xxs =
    if xxs = [] then
      acc
    else
      let
        xs = tl xxs
      in
        length (1 + acc) xs

  should return NONE - there is nothing we can expose
*)
val length2_fun_def = Define `
  length2_fun =
    If (Op Equal [Var 1; Op (Cons nil_tag) []])
       (Var 0)
       (Let [Call 5 (SOME 1) [Var 1] NONE]
            (Call 10 (SOME 2) [Op Add [Op (Const 1) []; Var 1]; Var 2] NONE))
  `;

(*
  length xxs =
    if xxs = [] then
      0
    else
      let
        xs = tl xxs
      in
        length xs + 1

  should optimize to SOME (...)
*)
val length3_fun_def = Define `
  length3_fun =
      If (Op Equal [Var 0; Op (Cons nil_tag) []])
         (Op (Const 0) [])
         (Let [Call 5 (SOME 1) [Var 0] NONE]
              (Op Add [Call 10 (SOME 2) [Var 0] NONE; Op (Const 1) []]))
  `;

(* Arbitrary example with a sub-expression carrying a tail call hidden inside
   an operation. While bad code, the algorithm could be extended to catch this
   as well.

   Should evaluate to NONE.
*)
val length4_fun_def = Define `
  length4_fun =
      If (Op Equal [Var 0; Op (Cons nil_tag) []])
         (Op (Const 0) [])
         (Let [Call 5 (SOME 1) [Var 0] NONE]
              (Op Add [Op (Const 1) [];
                       If (Var 2)
                          (Var 0)
                          (Call 10 (SOME 2) [Var 0] NONE)]))
  `;

(*
   foo 0 = 0
   foo n = (3 + foo n) + (5 + foo (n - 1))

   Optimizes to
*)
val foo_fun_def = Define `
  foo_fun: bvi$exp =
    If (Op (EqualInt 0) [Var 0])
       (Op (Const 0) [])
       (Op Add
         [Op Add [Op (Const 3) [];
                  Call 10 (SOME 2) [Var 0] NONE];
          Op Add [Op (Const 5) [];
                  Call 10 (SOME 2) [Op Sub [Var 0; Op (Const 1) []]] NONE
                 ]])`

val testop_def = Define `
  testop = 
    Op Add
      [Op Add [Op (Const 3) [];
               Call 10 (SOME 2) [Var 0] NONE];
       Op Add [Op (Const 5) [];
               Call 10 (SOME 2) [Op Sub [Var 0; Op (Const 1) []]] NONE
              ]]`;

val testop2_def = Define `
  testop2 = 
    Op Add [Op (Const 5) [];
            Call 10 (SOME 2) [Op Sub [Var 0; Op (Const 1) []]] NONE]`;

val test_expr0_def = Define `test_expr0 = Call 0 (SOME 127) [] NONE`;
val test_op_rewrite0 = EVAL ``op_rewrite (IntOp Plus) 127 test_expr0``
val test_binop_has_rec0 = EVAL ``binop_has_rec 127 (IntOp Plus) test_expr0``
val test_assoc_swap0 = EVAL ``assoc_swap (IntOp Plus) (Var 17) test_expr0``
val test_push_call0 = EVAL
  ``case op_binargs (assoc_swap (IntOp Plus) (Var 17) test_expr0) of
    | NONE => Var 333
    | SOME (e1, e2) =>
      push_call 999 (IntOp Plus) 777 e2 (args_from e1)`` 

val test_expr1_def = Define `
  test_expr1 = Op Add [Var 63; Call 0 (SOME 127) [] NONE]`
val test_op_rewrite1 = EVAL ``op_rewrite (IntOp Plus) 127 test_expr1``
val test_binop_has_rec1 = EVAL ``
  binop_has_rec 127 (IntOp Plus) (SND (op_rewrite (IntOp Plus) 127 test_expr1))``

val fac_tail_def = Define `
  fac_tail =
       (Op Mult
         [Var 0;
          Call 0 (SOME 1)
            [Op Sub [Var 0; Op (Const 1) []]]
            NONE])    
  `;

val fac_def = Define `
  fac =
    If (Op LessEq [Var 0; Op (Const 1) []])
       (Op (Const 1) [])
       (Op Mult
         [Var 0;
          Call 0 (SOME 1)
            [Op Sub [Var 0; Op (Const 1) []]]
            NONE])
  `;

val fac_tail_rewrite = EVAL ``tail_rewrite 2 (IntOp Times) 1 1 fac``
val fac_tail_op_rewrite = EVAL ``op_rewrite (IntOp Times) 1 fac_tail``
val fac_tail_rewrite_def = Define `
  fac_tail_rewrite =
    If (Op LessEq [Var 1; Op (Const 1) []])
       (Op Mult [Op (Const 1) []; Var 0])
         (Call 0 (SOME 1)
            [Op Mult [Var 1; Var 0]; 
             Op Sub [Var 1; Op (Const 1) []]] 
             NONE)
  `;

val test1 = EVAL ``optimize_single 9 2 1 length1_fun``;
val test1_tail_check = EVAL ``tail_check 2 length1_fun``;
(*val test1_tail_check2 = EVAL ``tail_check2 2 length1_fun``;*)
val test1_tail_rewrite = EVAL ``tail_rewrite 9 (IntOp Plus) 2 127 length1_fun``
(*val test1_tail_rewrite = EVAL ``tail_rewrite2 9 (IntOp Plus) 2 127 length1_fun``*)

val test2 = EVAL ``optimize_single 9 2 1 length2_fun``;
val test2_tail_check = EVAL ``tail_check 2 length2_fun``;
(*val test2_tail_check2 = EVAL ``tail_check2 2 length2_fun``;*)

val test3 = EVAL ``optimize_single 9 2 1 length3_fun``;
val test3_tail_check = EVAL ``tail_check 2 length3_fun``;
(*val test3_tail_check2 = EVAL ``tail_check2 2 length3_fun``;*)

val test4 = EVAL ``optimize_single 9 2 1 length4_fun``;
val test4_tail_check = EVAL ``tail_check 2 length4_fun``;
(*val test4_tail_check2 = EVAL ``tail_check2 2 length4_fun``;*)

val test5 = EVAL ``optimize_single 9 2 1 foo_fun``;
val test5_tail_check = EVAL ``tail_check 2 foo_fun``;
(*val test5_tail_check = EVAL ``tail_check2 2 foo_fun``;*)

val _ = export_theory();

