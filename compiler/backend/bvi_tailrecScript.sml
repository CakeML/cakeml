open preamble bviTheory
open backend_commonTheory;

(* Errors from dummy cases:

   Var 65534                  id_from_op 
   Call 23583 NONE [] NONE    comp
   Call 35505 NONE [] NONE    setup_call
   Var 65536                  push_call
   Var 65537                  mk_tailcall

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

(* Get the sub-expressions from a binary operation *)
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

(* Purity modulo call to `name` *)
val is_pure_mod_rec_def = Define `
  (is_pure_mod_rec name (Call _ (SOME n) _ _) ⇔ n = name) ∧
  (is_pure_mod_rec name exp                   ⇔ is_pure exp)
  `;

val op_binargs_exp_size = Q.store_thm ("op_binargs_exp_size",
  `∀xs x1 x2. op_binargs xs = SOME (x1, x2) ⇒
    (exp_size x1 < exp_size xs ∧ exp_size x2 < exp_size xs)`,
  Induct \\ fs [op_binargs_def]
  \\ Cases_on `l` \\ fs [op_binargs_def]
  \\ Cases_on `t` \\ fs [op_binargs_def]
  \\ Cases_on `t'` \\ fs [op_binargs_def]
  \\ rw [bviTheory.exp_size_def]);

(* Decompose a series of nested operator applications (provided the operators
   are the same) into a list of operands by in-order traversal. *)
val decomp_def = tDefine "decomp" `
  decomp op exp =
    if ¬op_eq op exp then
      [exp]
    else
      case op_binargs exp of
      | SOME (e1, e2) => decomp op e1 ++ decomp op e2
      | NONE          => [exp]`
  (WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ imp_res_tac op_binargs_exp_size \\ fs []);

(* Check if the call is recursive to `name` *)
val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ _) ⇔ d = SOME name) ∧
  (is_rec _    _                  ⇔ F)
  `;

(* Check if the expression is tail recursive wrt calls to `n` *)
val is_tailrec_def = Define `
  (is_tailrec n (If _ x2 x3)          ⇔ is_tailrec n x2 ∨ is_tailrec n x3) ∧
  (is_tailrec n (Let _ x1)            ⇔ is_tailrec n x1) ∧
  (is_tailrec n (Tick x1)             ⇔ is_tailrec n x1) ∧
  (is_tailrec n (Call _ (SOME m) _ _) ⇔ n = m) ∧
  (is_tailrec n _                     ⇔ F)`;

(* Ensure that all expressions /after/ the first recursive call in an in-order
   traversal are pure. *)
val all_pure_mod_rec_def = Define `
  (all_pure_mod_rec name has_rec []      ⇔ T) ∧
  (all_pure_mod_rec name has_rec (x::xs) ⇔
    if is_rec name x then
      all_pure_mod_rec name T xs
    else
      (has_rec ⇒ is_pure_mod_rec name x) ∧
      all_pure_mod_rec name has_rec xs)
  `;

(* Check call arguments for recursive calls. Returns the accepted
   decomposition if successful.

   TODO: This is wrong
*)
val arg_check_app_def = Define `
  arg_check_app op name op1 =
    let ds = decomp op op1 in
    let len = LENGTH ds in
      if len ≤ 1 then
        NONE
      else
        if is_rec name (HD ds) ∧ all_pure_mod_rec name F ds then
          SOME ds
        else
          NONE
  `;

(* Given that addition and multiplication are commutative operations, the place
   in which the recursive call appears is not important, as long as it appears
   at all, and that all expressions prior to this call in the in-order are pure,
   so that side-effects are not evaluated out of order. *)
val arg_check_int_def = Define `
  arg_check_int op name op1 =
    let ds = decomp op op1 in
    let len = LENGTH ds in
      if len ≤ 1 then
        NONE
      else
        if EXISTS (is_rec name) ds ∧ all_pure_mod_rec name F ds then
          SOME ds
        else
          NONE
  `;

(* Check tail positions for operators containing tail calls. The first
   operator found with optimizable sub-expressions is returned. *)

(*
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
      let op1 = from_op op in
        (case arg_check_int op1 name (Op op xs) of
        | SOME _ => SOME op1
        | _ => NONE)
    else NONE)`;
*)

(* Ensure that return values in sub-expressions are literals, arithmetic, or
   recursive calls to the function itself.

   TODO: All tail positions will need to be modified with some no-op arithmetic
   before this point, e.g. x |-> x + 0.
*)
val ok_tail_type_def = Define `
  (ok_tail_type name (Op op _)             ⇔ is_arithmetic op) ∧
  (ok_tail_type name (Call _ (SOME n) _ _) ⇔ n = name) ∧
  (ok_tail_type name (Let _ x1)            ⇔ ok_tail_type name x1) ∧
  (ok_tail_type name (Tick x1)             ⇔ ok_tail_type name x1) ∧
  (ok_tail_type name (If _ x2 x3)          ⇔
    ok_tail_type name x2 ∧ ok_tail_type name x3) ∧
  (ok_tail_type name _                     ⇔ F)
  `;

(* Pick out the first recursive call to `name` and return it together with the
   list up to and following that point so that

     comp name qs xs = (front, call, back) ⇒ front ++ [call] ++ back = xs

  TODO could return the parameters to the call instead *)
val comp_def = Define `
  (comp name qs []      = (REVERSE qs, Call 23583 NONE [] NONE, [])) ∧
  (comp name qs (x::xs) =
    if is_rec name x then (REVERSE qs, x, xs) else comp name (x::qs) xs)
  `;

(* TODO this could take parameters (t,d,as,h) *)
val setup_call_def = Define `
  (setup_call n acc op exp (SOME (t,d,as,hdl)) =
    Call t (SOME n) ((apply_op op (Var acc) exp)::as) hdl) ∧
  (setup_call n acc op exp NONE = Call 35505 NONE [] NONE) (* dummy *)
  `;

(* We REVERSE xs since we want the /last/ recursive call *)
val mk_tailcall_int_def = Define `
  mk_tailcall_int n op name acc xs =
    let (front, call, back) = comp name [] (REVERSE xs) in
    let ys = (REVERSE back) ++ (REVERSE front) in
      setup_call n acc op (FOLDR (apply_op op) (LAST ys) (FRONT ys)) 
                          (args_from call)
  `;

(* Attempt to rewrite tail positions matching `op` with tail calls. All other
   tail positions are rewritten by applying the accumulator from the right. *)

(*
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
  (tail_rewrite n op name acc exp =
    case arg_check_int op name exp of
    | NONE    => apply_op op exp (Var acc)
    | SOME ds => mk_tailcall_int n op name acc ds)
  `;

*)

(* -------------------------------------------------------------------------- *)


(* Recursively rewrite. Try to achieve things like:

     1 + length xs |-> length xs + 1    since is_pure 1

   For instance, if we receive (op_rewrite x1, op_rewrite x2) = 

     (1) (e1, f1 xs + y) ∧ is_pure e1     |-> (T, f1 xs + (y + e1)) 
     (2) (f1 xs + y, e2) ∧ is_pure e2     |-> (T, f1 xs + (y + e2))
     (3) (f1 xs + y, f2 xs + z)           |-> (T, f2 xs + (y + (f1 xs + z)))
     (4) otherwise                        |-> (F, apply_op x1 x2)

   In (3), f1, f2 are both recursive calls to "our" function. to preserve order
   of potential side-effects, use the rightmost one outermost (evaluate last).

   Finally, if there was a rewrite, i.e. (T, exp) returns, then we know that
   
     ∃ticks args hdl exp2. 
       exp = apply_op op (Call ticks (SOME name) args hdl) exp2

   We then rewrite this to 

     Call ticks (SOME n) (apply_op op (Var acc) exp2 :: args) hdl.

   Otherwise if we get (F, exp) we just replace it with

     apply_op op exp (Var acc)

   Hopefully we can derive some lemmas because correctness locally here seems to
   imply correcntess globally when composing the expressions.

   Because of associativity and commutativity, the original exp and the result 
   in (F/T, exp) should be equivalent. Moreover, each step in the recursion
   should produce an equivalent result. If we have some associativity lemma
   for apply op we should be able to do induction on op_rewrite and say that

      evaluate ([exp], env, s) = (r, t) ∧
      r ≠ Rerr (Rabort Rtype_error) ⇒ 
        case op_rewrite op exp of
        | (F, exp2) => exp = exp2 
        | (T, exp2) => evaluate ([exp2], env, s) = (r, t)

   _Maybe_.
*)

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
val ac_swap_def = Define `
  ac_swap op from into =
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
          | (T, T) => (T, ac_swap op y1 y2)
          | (T, F) => if is_pure y2 then (T, ac_swap op y2 y1) else (F, exp)
          | (F, T) => if is_pure y1 then (T, ac_swap op y1 y2) else (F, exp)
  `
  (WF_REL_TAC `measure (exp_size o SND o SND)`
  \\ rpt strip_tac
  \\ drule exp_size_op_binargs
  \\ fs []);

(* Use the rewrite function as the new ``tail_check``. If it succeeds it should
   be fine?
*)
   
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
  (push_call n op acc exp (SOME (t, d, a, h)) =
    Call t (SOME n) (apply_op op exp (Var acc) :: a) h) ∧
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

(* New tail_rewrite function *)
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

(* -------------------------------------------------------------------------- *)

(* If the type of the tail positions is determined to be fine we check if there
   is some tail position that can be optimized. *)
val optimize_check_def = Define `
  optimize_check name exp =
    if ¬ok_tail_type name exp then
      NONE
    else
      tail_check name exp
  `;

(* The accumulator is the first variable in the environment. However,
   all other variables in the expression need to be shifted up one step.

   If we wrap the expression in a Let expression we won't have to traverse the
   expression and selectively shift some variables up; pretending that the
   accumulator is at the very end of the environment when optimizing will
   suffice. In short, we prepend the environment with its tail, and the
   accumulator ends up in the right place. *)
val let_wrap_def = Define `
  let_wrap num_args exp =
    Let (GENLIST (λi. Var (i + 1)) num_args) exp
  `;

(* Create auxilliary definition (use the "old" name). *)
val mk_aux_call_def = Define `
  mk_aux_call name num_args id =
    Call 0 (SOME name) (id :: GENLIST (λi. Var (i + 0)) num_args) NONE
  `;

(* Perform the full rewrite and generate an auxilliary function. *)
val optimize_single_def = Define `
  optimize_single n name num_args exp =
    case optimize_check name exp of
    | NONE => NONE
    | SOME op =>
        let opt = let_wrap num_args (tail_rewrite n op name num_args exp) in
        let aux = mk_aux_call n num_args (id_from_op op) in
          SOME (aux, opt)
  `;

(* Applies the tail-recursion optimization on all entries in the code table.
   Requires the first free name in the code table following the renaming in
   BVL-to-BVI. *)
val optimize_all_def = Define `
  (optimize_all n code []                    acc = REVERSE acc) ∧
  (optimize_all n code ((nm, args, exp)::xs) acc =
    case optimize_single n nm args exp of
    | NONE => optimize_all n code xs ((nm, args, exp)::acc)
    | SOME (exp_aux, exp_opt) =>
        let code1 = insert nm (args, exp_aux) code in
        let code2 = insert n (args + 1, exp_opt) code1 in
          optimize_all (n + 2) code2 xs
            ((nm, args, exp_aux)::(n, args + 1, exp_opt)::acc))
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
val test_ac_swap0 = EVAL ``ac_swap (IntOp Plus) (Var 17) test_expr0``
val test_push_call0 = EVAL
  ``case op_binargs (ac_swap (IntOp Plus) (Var 17) test_expr0) of
    | NONE => Var 333
    | SOME (e1, e2) =>
      push_call 999 (IntOp Plus) 777 e2 (args_from e1)`` 

val test_expr1_def = Define `
  test_expr1 = Op Add [Var 63; Call 0 (SOME 127) [] NONE]`
val test_op_rewrite1 = EVAL ``op_rewrite (IntOp Plus) 127 test_expr1``
val test_binop_has_rec1 = EVAL ``
  binop_has_rec 127 (IntOp Plus) (SND (op_rewrite (IntOp Plus) 127 test_expr1))``


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

