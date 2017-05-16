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

(* TODO defined in bviSemTheory, should be moved to bviTheory? 
   On the other hand: its use here is temporary.
*)
val small_enough_int_def = Define `
  small_enough_int i <=> -268435457 <= i /\ i <= 268435457`;

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
  assoc_op = Plus
           | Times
           | Noop
  `;

val to_op_def = Define `
  (to_op Plus  = Add) ∧
  (to_op Times = Mult) ∧
  (to_op Noop  = Const 0)
  `;

val from_op_def = Define `
  (from_op Add  = Plus) ∧
  (from_op Mult = Times) ∧
  (from_op _    = Noop)
  `;

val op_eq_def = Define `
  (op_eq Plus  (Op Add _)             ⇔ T) ∧
  (op_eq Times (Op Mult _)            ⇔ T) ∧
  (op_eq _     _                      ⇔ F)
  `;

val apply_op_def = Define `
  apply_op op e1 e2 = Op (to_op op) [e1; e2]
  `;

val id_from_op_def = Define `
  (id_from_op Plus  = bvi$Op (Const 0) []) ∧
  (id_from_op Times = bvi$Op (Const 1) []) ∧
  (id_from_op Noop  = bvi$Var 65537)
  `;

val op_binargs_def = Define `
  op_binargs (bvi$Op _ [e1; e2]) = SOME (e1, e2) ∧
  op_binargs _                   = NONE
  `;

val MEM_exp_size_imp = Q.store_thm ("MEM_exp_size_imp",
  `∀xs a. MEM a xs ⇒ bvi$exp_size a < exp2_size xs`,
  Induct \\ rw [bviTheory.exp_size_def] \\ res_tac \\ fs []);

(* TODO parametrise on operator *)
val no_err_def = Define `
  (no_err (Op (Const i) [])  ⇔ small_enough_int i) ∧
  (no_err (Op Add [x1; x2])  ⇔ no_err x1 ∧ no_err x2) ∧
  (no_err (Op Mult [x1; x2]) ⇔ no_err x1 ∧ no_err x2) ∧
  (no_err _                  ⇔ F)
  `;

val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ NONE) ⇔ d = SOME name) ∧
  (is_rec _    _                     ⇔ F)
  `;

val ok_tail_type_def = Define `
  (ok_tail_type (Op op _)    ⇔ is_arithmetic op) ∧
  (ok_tail_type (Let _ x1)   ⇔ ok_tail_type x1) ∧
  (ok_tail_type (Tick x1)    ⇔ ok_tail_type x1) ∧
  (ok_tail_type (If _ x2 x3) ⇔ ok_tail_type x2 ∧ ok_tail_type x3) ∧
  (ok_tail_type _            ⇔ F)
  `;

val binop_has_rec_def = Define `
  binop_has_rec name op exp ⇔
    is_rec name exp ∨ 
    op_eq op exp ∧ 
      (case op_binargs exp of
      | NONE => F
      | SOME (x1, x2) => is_rec name x1 ∧ no_err x2)
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

val assoc_swap_def = Define `
  assoc_swap op from into =
    if ¬op_eq op into then
      apply_op op into from
    else
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
          | (T, T) => (F, exp)
          | (T, F) => if no_err y2 then (T, assoc_swap op y2 y1) else (F, exp)
          | (F, T) => if no_err y1 then (T, assoc_swap op y1 y2) else (F, exp)
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
    Call ticks (SOME n) (args ++ [apply_op op exp (Var acc)]) handler) ∧
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

val tail_rewrite_aug_def = Define `
  (tail_rewrite_aug n op name acc (Let xs x) =
    let (r, y) = tail_rewrite_aug n op name acc x
    in (r, Let xs y)) ∧
  (tail_rewrite_aug n op name acc (Tick x) =
    let (r, y) = tail_rewrite_aug n op name acc x
    in (r, Tick y)) ∧
  (tail_rewrite_aug n op name acc (Raise x) = (F, Raise x)) ∧
  (tail_rewrite_aug n op name acc (If x1 x2 x3) =
    let (r2, y2) = tail_rewrite_aug n op name acc x2 in
    let (r3, y3) = tail_rewrite_aug n op name acc x3 in
    let z2 = if r2 then y2 else apply_op op x2 (Var acc) in
    let z3 = if r3 then y3 else apply_op op x3 (Var acc) in
      (r2 ∨ r3, If x1 z2 z3)) ∧
  (tail_rewrite_aug n op name acc exp =
    case op_rewrite op name exp of
      (F, _) => (F, apply_op op exp (Var acc))
    | (T, exp') => 
        (case op_binargs exp' of
          NONE => (F, apply_op op exp (Var acc))
        | SOME (call, exp'') =>
            (T, push_call n op acc exp'' (args_from call))))
  `;

val optimize_check_def = Define `
  optimize_check name exp =
    if ¬ok_tail_type exp then
      NONE
    else
      tail_check name exp
  `;

val let_wrap_def = Define `
  let_wrap num_args id exp =
    Let ((GENLIST (λi. Var i) num_args) ++ [id]) exp
  `;

val mk_aux_call_def = Define `
  mk_aux_call name num_args id =
    Call 0 (SOME name) (id :: GENLIST (λi. Var (i + 0)) num_args) NONE
  `;

val optimize_single_def = Define `
  optimize_single n name num_args exp =
    case optimize_check name exp of
    | NONE => NONE
    | SOME op =>
        let opt = tail_rewrite n op name num_args exp in
        let aux = let_wrap num_args (id_from_op op) opt in
          SOME (aux, opt)
  `;

val optimize_single_aug_def = Define `
  optimize_single_aug n name num_args exp =
    case optimize_check name exp of
      NONE => NONE
    | SOME op =>
      let (_, opt) = tail_rewrite_aug n op name num_args exp in
      let aux = let_wrap num_args (id_from_op op) opt in
        SOME (aux, opt)
  `;

val optimize_prog_def = Define `
  (optimize_prog n [] = []) ∧
  (optimize_prog n ((nm, args, exp)::xs) =
    case optimize_single_aug n nm args exp of
    | NONE => (nm, args, exp)::optimize_prog n xs
    | SOME (exp_aux, exp_opt) =>
        (nm, args, exp_aux)::(n, args + 1, exp_opt)::optimize_prog (n + 2) xs)
  `;

val _ = export_theory();

