open preamble bviTheory
open backend_commonTheory;

(* Errors from dummy cases:

   Var 65534                  id_from_op
   Var 65536                  push_call
   Var 65537                  mk_tailcall
*)

val _ = new_theory "bvi_tailrec";

(* TODO defined in bviSemTheory, should be moved to bviTheory?
   On the other hand: its use here is temporary.
*)
val small_int_def = Define `
  small_int i <=> -268435457 <= i /\ i <= 268435457`;

val MEM_exp_size_imp = Q.store_thm ("MEM_exp_size_imp",
  `∀xs a. MEM a xs ⇒ bvi$exp_size a < exp2_size xs`,
  Induct \\ rw [bviTheory.exp_size_def] \\ res_tac \\ fs []);

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
  (op_eq Plus  (Op Add _)  ⇔ T) ∧
  (op_eq Times (Op Mult _) ⇔ T) ∧
  (op_eq _     _           ⇔ F)
  `;

val apply_op_def = Define `
  apply_op op e1 e2 = Op (to_op op) [e1; e2]
  `;

val id_from_op_def = Define `
  (id_from_op Plus  = bvi$Op (Const 0) []) ∧
  (id_from_op Times = bvi$Op (Const 1) []) ∧
  (id_from_op Noop  = bvi$Var 65537)
  `;

val get_bin_args_def = Define `
  get_bin_args (bvi$Op _ [e1; e2]) = SOME (e1, e2) ∧
  get_bin_args _                   = NONE
  `;

val exp_size_get_bin_args = Q.store_thm ("exp_size_get_bin_args",
  `∀x x1 x2.
     get_bin_args x = SOME (x1, x2) ⇒
       exp_size x1 < exp_size x ∧
       exp_size x2 < exp_size x`,
  Induct \\ fs [get_bin_args_def]
  \\ ntac 3 strip_tac
  \\ Cases_on `l` \\ simp [get_bin_args_def]
  \\ Cases_on `t` \\ simp [get_bin_args_def]
  \\ Cases_on `t'` \\ simp [get_bin_args_def]
  \\ fs [bviTheory.exp_size_def]);

(* TODO parametrise on operator *)
val no_err_def = Define `
  (no_err (Op (Const i) [])  ⇔ small_int i) ∧
  (no_err (Op Add [x1; x2])  ⇔ no_err x1 ∧ no_err x2) ∧
  (no_err (Op Mult [x1; x2]) ⇔ no_err x1 ∧ no_err x2) ∧
  (no_err _                  ⇔ F)
  `;

val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ NONE) ⇔ d = SOME name) ∧
  (is_rec _    _                     ⇔ F)
  `;

val is_ok_type_def = Define `
  (is_ok_type (Op op _)    ⇔ is_arithmetic op) ∧
  (is_ok_type (Let _ x1)   ⇔ is_ok_type x1) ∧
  (is_ok_type (Tick x1)    ⇔ is_ok_type x1) ∧
  (is_ok_type (If _ x2 x3) ⇔ is_ok_type x2 ∧ is_ok_type x3) ∧
  (is_ok_type _            ⇔ F)
  `;

val is_rec_or_rec_binop_def = Define `
  is_rec_or_rec_binop name op exp ⇔
    is_rec name exp ∨
    op_eq op exp ∧
      (case get_bin_args exp of
      | NONE => F
      | SOME (x1, x2) => is_rec name x1 ∧ no_err x2)
  `;

val assoc_swap_def = Define `
  assoc_swap op from into =
    if ¬op_eq op into then
      apply_op op into from
    else
      case get_bin_args into of
      | NONE => apply_op op into from
      | SOME (x1, x2) => apply_op op x1 (apply_op op from x2)
  `;

val rewrite_op_def = tDefine "rewrite_op" `
  rewrite_op op name exp =
    if ¬op_eq op exp then
      (F, exp)
    else
      case get_bin_args exp of
      | NONE => (F, exp)
      | SOME (x1, x2) =>
        let (r1, y1) = rewrite_op op name x1 in
        let (r2, y2) = rewrite_op op name x2 in
          case (is_rec_or_rec_binop name op y1,
                is_rec_or_rec_binop name op y2) of
          | (F, F) => (F, exp)
          | (T, T) => (F, exp)
          | (T, F) => if no_err y2 then (T, assoc_swap op y2 y1) else (F, exp)
          | (F, T) => if no_err y1 then (T, assoc_swap op y1 y2) else (F, exp)
  `
  (WF_REL_TAC `measure (exp_size o SND o SND)`
  \\ rpt strip_tac
  \\ drule exp_size_get_bin_args
  \\ fs []);

val tail_is_ok_def = Define `
  (tail_is_ok name (Var _)        = NONE) ∧
  (tail_is_ok name (Let _ x1)     = tail_is_ok name x1) ∧
  (tail_is_ok name (Tick x1)      = tail_is_ok name x1) ∧
  (tail_is_ok name (Raise x1)     = NONE) ∧
  (tail_is_ok name (If _ x2 x3)   =
    case tail_is_ok name x2 of
    | SOME op => SOME op
    | _       => tail_is_ok name x3) ∧
  (tail_is_ok name (Call _ _ _ _) = NONE) ∧
  (tail_is_ok name (Op op xs)     =
    if op = Add ∨ op = Mult then
      let iop = from_op op in
        (case rewrite_op iop name (Op op xs) of
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
    case rewrite_op op name exp of
    | (F, exp2) => apply_op op exp2 (Var acc)
    | (T, exp2) =>
        (case get_bin_args exp2 of
        | NONE => Var 65537 (* dummy *)
        | SOME (call, exp3) =>
          push_call n op acc exp3 (args_from call))
  `;

val rewrite_tail_def = Define `
  (rewrite_tail n op name acc (Let xs x) =
    let (r, y) = rewrite_tail n op name (acc + LENGTH xs) x
    in (r, Let xs y)) ∧
  (rewrite_tail n op name acc (Tick x) =
    let (r, y) = rewrite_tail n op name acc x
    in (r, Tick y)) ∧
  (rewrite_tail n op name acc (Raise x) = (F, Raise x)) ∧
  (rewrite_tail n op name acc (If x1 x2 x3) =
    let (r2, y2) = rewrite_tail n op name acc x2 in
    let (r3, y3) = rewrite_tail n op name acc x3 in
    let z2 = if r2 then y2 else apply_op op x2 (Var acc) in
    let z3 = if r3 then y3 else apply_op op x3 (Var acc) in
      (r2 ∨ r3, If x1 z2 z3)) ∧
  (rewrite_tail n op name acc exp =
    case rewrite_op op name exp of
      (F, _) => (F, apply_op op exp (Var acc))
    | (T, exp') =>
        (case get_bin_args exp' of
          NONE => (F, apply_op op exp (Var acc))
        | SOME (call, exp'') =>
            (T, push_call n op acc exp'' (args_from call))))
  `;

val check_exp_def = Define `
  check_exp name exp =
    if ¬is_ok_type exp then
      NONE
    else
      tail_is_ok name exp
  `;

val let_wrap_def = Define `
  let_wrap num_args id exp =
    Let ((GENLIST (λi. Var i) num_args) ++ [id]) exp
  `;

val mk_aux_call_def = Define `
  mk_aux_call name num_args id =
    Call 0 (SOME name) (id :: GENLIST (λi. Var (i + 0)) num_args) NONE
  `;

val compile_exp_def = Define `
  compile_exp n name num_args exp =
    case check_exp name exp of
      NONE => NONE
    | SOME op =>
      let (_, opt) = rewrite_tail n op name num_args exp in
      let aux = let_wrap num_args (id_from_op op) opt in
        SOME (aux, opt)
  `;

val compile_prog_def = Define `
  (compile_prog n [] = (n, [])) ∧
  (compile_prog n ((nm, args, exp)::xs) =
    case compile_exp n nm args exp of
    | NONE =>
        let (n1, ys) = compile_prog n xs in
          (n1, (nm, args, exp)::ys)
    | SOME (exp_aux, exp_opt) =>
        let (n1, ys) = compile_prog (n + 2) xs in
        (n1, (nm, args, exp_aux)::(n, args + 1, exp_opt)::ys))
  `;

val _ = export_theory();

