(*
  A compiler phase that turns some non-tail-recursive functions into
  tail-recursive functions.
*)

open preamble bviTheory backend_commonTheory

val _ = new_theory "bvi_tailrec";

val _ = set_grammar_ancestry["bvi", "backend_common"];
val _ = temp_tight_equality();

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

val dummy_def = Define `dummy = bvi$Var 1234567890`;

Theorem MEM_exp_size_imp:
   ∀xs a. MEM a xs ⇒ bvi$exp_size a < exp2_size xs
Proof
  Induct \\ rw [bviTheory.exp_size_def] \\ res_tac \\ fs []
QED

(* TODO defined in bviSemTheory, should be moved to bviTheory?
   On the other hand: its use here is temporary.
*)
val small_int_def = Define `
  small_int (i:int) <=> -268435457 <= i /\ i <= 268435457`;

val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ NONE) ⇔ d = SOME name) ∧
  (is_rec _    _                     ⇔ F)
  `;

Theorem is_rec_PMATCH:
   !expr. is_rec name expr =
    case expr of
      Call _ d _ NONE => d = SOME name
    | _               => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ Cases \\ fs [is_rec_def]
  \\ rename1 `Call _ _ _ hdl`
  \\ Cases_on `hdl` \\ fs [is_rec_def]
QED

val is_const_def = Define `
  (is_const (Const i) <=> small_int i) /\
  (is_const _         <=> F)`;

Theorem is_const_PMATCH:
   !op. is_const op =
    case op of
      Const i => small_int i
    | _       => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ Cases \\ rw [is_const_def]
QED

val _ = export_rewrites ["is_const_def"];

val _ = Datatype `
  assoc_op = Plus
           | Times
           | Append
           | Noop`;

val _ = Datatype `v_ty = Int | List | Any`;

val op_type_def = Define `
  op_type Append = List /\
  op_type Noop   = Any /\
  op_type _      = Int`;

val to_op_def = Define `
  to_op Plus   = Add        /\
  to_op Times  = Mult       /\
  to_op Append = ListAppend /\
  to_op Noop   = Mod
  `;

val from_op_def = Define `
  from_op op =
    if op = Add then Plus
    else if op = Mult then Times
    else if op = ListAppend then Append
    else Noop
  `;

Theorem from_op_PMATCH:
   !op.
    from_op op =
      case op of
        Add        => Plus
      | Mult       => Times
      | ListAppend => Append
      | _          => Noop
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [from_op_def]
QED

val from_op_thm = save_thm("from_op_thm[simp]",
  map (fn tm => EVAL ``from_op ^tm``)
  (TypeBase.case_def_of ``:closLang$op``
   |> CONJUNCTS |> map (el 1 o #2 o strip_comb o lhs o concl o SPEC_ALL))
  |> LIST_CONJ)

val op_eq_def = Define `
  (op_eq Plus   (Op op xs) <=> op = Add) /\
  (op_eq Times  (Op op xs) <=> op = Mult) /\
  (op_eq Append (Op op xs) <=> op = ListAppend) /\
  (op_eq _      _          <=> F)`;

Theorem op_eq_PMATCH:
   !a expr.
     op_eq a expr =
       case expr of
         Op op xs =>
           (case a of
             Plus   => op = Add
           | Times  => op = Mult
           | Append => op = ListAppend
           | _      => F)
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ Cases \\ rw [op_eq_def]
QED

Theorem op_eq_to_op[simp]:
   ∀iop op xs.
      op_eq iop (Op op xs)
      ⇔
      op = to_op iop ∧ iop ≠ Noop
Proof
  Cases \\ Cases \\ fs [op_eq_def, to_op_def]
QED

val apply_op_def = Define `
  apply_op op e1 e2 = Op (to_op op) [e1; e2]
  `;

val id_from_op_def = Define `
  id_from_op Plus   = bvi$Op (Const 0) []       /\
  id_from_op Times  = bvi$Op (Const 1) []       /\
  id_from_op Append = bvi$Op (Cons nil_tag) []  /\
  id_from_op Noop   = dummy
  `;

val index_of_def = Define `
  (index_of (bvi$Var i) = SOME i) ∧
  (index_of _           = NONE)
  `;

Theorem index_of_PMATCH:
   !expr.
     index_of expr =
       case expr of
         Var i => SOME i
       | _     => NONE
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [index_of_def]
QED

val args_from_def = Define `
  (args_from (bvi$Call t (SOME d) as hdl) = SOME (t, d, as, hdl)) ∧
  (args_from _                            = NONE)
  `;

Theorem args_from_PMATCH:
   !expr.
     args_from expr =
       case expr of
         Call t (SOME d) as hdl => SOME (t,d,as,hdl)
       | _                      => NONE
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [args_from_def]
  \\ rename1 `Call _ nm _ _`
  \\ Cases_on `nm` \\ rw [args_from_def]
QED

val get_bin_args_def = Define `
  get_bin_args op =
    dtcase op of
    | bvi$Op _ [e1; e2] => SOME (e1, e2)
    | _ => NONE`;

Theorem get_bin_args_PMATCH:
   !op.
     get_bin_args op =
       case op of
         Op _ [e1; e2] => SOME (e1,e2)
       | _             => NONE
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [get_bin_args_def]
QED

Theorem exp_size_get_bin_args:
   ∀x x1 x2.
     get_bin_args x = SOME (x1, x2) ⇒
       exp_size x1 + exp_size x2 < exp_size x
Proof
  Induct
  \\ rw [get_bin_args_def, exp_size_def]
  \\ every_case_tac
  \\ fs [exp_size_def]
QED

val opbinargs_def = Define `
  opbinargs opr exp = if ~op_eq opr exp then NONE else get_bin_args exp`;

val try_update_def = Define `
  (try_update vty NONE     ts = ts) ∧
  (try_update vty (SOME n) ts =
    if n < LENGTH ts then
      if EL n ts = Any then
        TAKE n ts ++ [vty] ++ DROP (n + 1) ts
      else ts
    else ts)`;

(* --- Checking termination guarantees --- *)

val is_arith_def = Define `
  is_arith op =
    dtcase op of
      Add  => T
    | Sub  => T
    | Mult => T
    | _    => F`;

Theorem is_arith_PMATCH:
   !op.
     is_arith op =
       case op of
         Add  => T
       | Sub  => T
       | Mult => T
       | _    => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [is_arith_def]
QED

val is_rel_def = Define `
  is_rel op =
    dtcase op of
      Less      => T
    | LessEq    => T
    | Greater   => T
    | GreaterEq => T
    | _         => F`;

Theorem is_rel_PMATCH:
   !op.
     is_rel op =
       case op of
         Less      => T
       | LessEq    => T
       | Greater   => T
       | GreaterEq => T
       | _         => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [is_rel_def]
QED

val term_ok_int_def = tDefine "term_ok_int" `
  (term_ok_int ts expr =
    dtcase expr of
      Var i => if i < LENGTH ts then EL i ts = Int else F
    | Op op xs =>
        (dtcase get_bin_args expr of
          NONE       => xs = [] /\ is_const op
        | SOME (x,y) => is_arith op /\ term_ok_int ts x /\ term_ok_int ts y)
    | _ => F)`
  (WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ imp_res_tac exp_size_get_bin_args
  \\ fs [bviTheory.exp_size_def]);

val term_ok_int_ind = save_thm ("term_ok_int_ind",
  theorem "term_ok_int_ind" |> SIMP_RULE (srw_ss()) []);

val term_ok_any_def = tDefine "term_ok_any" `
  (term_ok_any ts list (Var i) <=>
    if ~list then i < LENGTH ts
    else if i < LENGTH ts then EL i ts = List
    else F) /\
  (term_ok_any ts list (Op op xs) <=>
    dtcase get_bin_args (Op op xs) of
      NONE       => xs = [] /\ if list then op = Cons 0 else is_const op
    | SOME (x,y) =>
        if op = ListAppend then term_ok_any ts T x /\ term_ok_any ts T y
        else if ~list /\ is_arith op then term_ok_int ts x /\ term_ok_int ts y
        else if ~list /\ is_rel op   then term_ok_int ts x /\ term_ok_int ts y
        else if op = Cons 0 then term_ok_any ts T x /\ term_ok_any ts F y
        else F) /\
  (term_ok_any ts list expr <=> F)`
  (WF_REL_TAC `measure (exp_size o SND o SND)` \\ rw []
   \\ imp_res_tac exp_size_get_bin_args
   \\ fs [bviTheory.exp_size_def, closLangTheory.op_size_def]);

Theorem is_op_thms:
   ~is_arith (Cons 0) /\ ~is_arith ListAppend /\
   ~is_rel (Cons 0) /\ ~is_rel ListAppend /\
   (!op. op <> ListAppend /\ is_arith op <=> is_arith op) /\
   (!op. op <> ListAppend /\ ~is_arith op /\ is_rel op <=> is_rel op) /\
   (!op. ~is_arith op /\ ~is_rel op /\ op = Cons 0 <=> op = Cons 0) /\
   (!op. op <> ListAppend /\ op = Cons 0 <=> op = Cons 0)
Proof
  rw [is_arith_def, is_rel_def] \\ fs []
  \\ Cases_on `op` \\ fs []
QED

val term_ok_any_ind = save_thm ("term_ok_any_ind",
  theorem "term_ok_any_ind" |> SIMP_RULE (srw_ss()) [is_op_thms]);

(* TODO the translator does not accept this with the induction theorem
   above (yet):

Theorem term_ok_any_PMATCH:
   term_ok_any ts list expr =
     case expr of
       Var i => if ~list then i < LENGTH ts
                else if i < LENGTH ts then EL i ts = List
                else F
     | Op op xs =>
          (dtcase get_bin_args (Op op xs) of
            NONE       => xs = [] /\ if list then op = Cons 0 else is_const op
          | SOME (x,y) =>
              if op = ListAppend then term_ok_any ts T x /\ term_ok_any ts T y
              else if ~list /\ is_arith op then term_ok_int ts x /\ term_ok_int ts y
              else if ~list /\ is_rel op   then term_ok_int ts x /\ term_ok_int ts y
              else if op = Cons 0 then term_ok_any ts T x /\ term_ok_any ts F y
              else F)
     | _ => F
Proof
  Cases_on `expr` \\ once_rewrite_tac [term_ok_any_def] \\ fs []
QED
*)

val term_ok_def = Define `
  term_ok ts ty expr =
    dtcase ty of
      Any  => term_ok_any ts F expr
    | Int  => term_ok_int ts expr
    | List => term_ok_any ts T expr`;

(* --- Simple tail checking before rewriting --- *)

(* Swap arguments when commutative *)
val try_swap_def = Define `
  (try_swap loc Append exp = exp) /\
  (try_swap loc opr    exp =
    dtcase opbinargs opr exp of
      NONE => exp
    | SOME (l, r) =>
        if is_rec loc l then apply_op opr r l else exp)`;

(* Check if ok to lift xs into accumulator *)
val check_op_def = Define `
  check_op ts opr loc exp =
    dtcase opbinargs opr (try_swap loc opr exp) of
      NONE => NONE
    | SOME (xs, f) =>
        if is_rec loc f /\ term_ok ts (op_type opr) xs then
          SOME (apply_op opr xs f)
        else
          NONE`

(* --- Type analysis --- *)

val decide_ty_def = Define `
  (decide_ty Int  Int  = Int)  /\
  (decide_ty List List = List) /\
  (decide_ty _    _    = Any)`;

Theorem decide_ty_PMATCH:
   !ty1 ty2.
     decide_ty ty1 ty2 =
       case (ty1,ty2) of
         (Int, Int)   => Int
       | (List, List) => List
       | _            => Any
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ Cases \\ rw [decide_ty_def]
QED

val _ = export_rewrites ["decide_ty_def"]

val LAST1_def = Define `
  LAST1 []      = NONE   /\
  LAST1 [x]     = SOME x /\
  LAST1 (x::xs) = LAST1 xs`;

val update_context_def = Define `
  update_context ty ts x1 x2 =
    try_update ty (index_of x2) (try_update ty (index_of x1) ts)`;

val arg_ty_def = Define `
  (arg_ty (Const i)  = if small_int i then Int else Any) /\
  arg_ty Add        = Int /\
  arg_ty Sub        = Int /\
  arg_ty Mult       = Int /\
  arg_ty Div        = Int /\
  arg_ty Mod        = Int /\
  arg_ty LessEq     = Int /\
  arg_ty Less       = Int /\
  arg_ty Greater    = Int /\
  arg_ty GreaterEq  = Int /\
  arg_ty ListAppend = List /\
  arg_ty _          = Any`;

Theorem arg_ty_PMATCH:
   !op.
     arg_ty op =
       case op of
         Add        => Int
       | Sub        => Int
       | Mult       => Int
       | Div        => Int
       | Mod        => Int
       | LessEq     => Int
       | Less       => Int
       | Greater    => Int
       | GreaterEq  => Int
       | ListAppend => List
       | Const i    => if small_int i then Int else Any
       | _          => Any
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [arg_ty_def]
QED

val op_ty_def = Define `
  (op_ty Add        = Int) /\
  (op_ty Sub        = Int) /\
  (op_ty Mult       = Int) /\
  (op_ty Div        = Int) /\
  (op_ty Mod        = Int) /\
  (op_ty ListAppend = List) /\
  (op_ty (Cons tag) = if tag = nil_tag \/ tag = cons_tag then List else Any) /\
  (op_ty (Const i)  = if small_int i then Int else Any) /\
  (op_ty _          = Any)`;

Theorem op_ty_PMATCH:
   !op.
     op_ty op =
       case op of
         Add        => Int
       | Sub        => Int
       | Mult       => Int
       | Div        => Int
       | Mod        => Int
       | ListAppend => List
       | Cons tag   => if tag = cons_tag \/ tag = nil_tag then List else Any
       | Const i    => if small_int i then Int else Any
       | _          => Any
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [op_ty_def]
QED

(* Gather information about expressions:

     - Build context by following order of evaluation during recursion
       and set variable to Int only if interpretation of the expression would
       result in Rerr (Rabort Rtype_error) otherwise.
     - Check if tail positions are arithmetic or variables typed as Int in
       context.
     - Check if tail positions carry suitable operation (Add/Mult) and track
       branch of origin for the operation in conditionals.
*)

val scan_expr_def = tDefine "scan_expr" `
  (scan_expr ts loc [] = []) ∧
  (scan_expr ts loc (x::y::xs) =
    let (tx, ty, r, op) = HD (scan_expr ts loc [x]) in
      (tx, ty, r, op)::scan_expr tx loc (y::xs)) /\
  (scan_expr ts loc [Var n] =
    let ty = if n < LENGTH ts then EL n ts else Any in
      [(ts, ty, F, NONE)]) ∧
  (scan_expr ts loc [If xi xt xe] =
    let (ti, tyi, _, oi) = HD (scan_expr ts loc [xi]) in
    let (tt, ty1, _, ot) = HD (scan_expr ti loc [xt]) in
    let (te, ty2, _, oe) = HD (scan_expr ti loc [xe]) in
    let op = dtcase ot of NONE => oe | _ => ot in
    let ty = dtcase op of
               NONE => decide_ty ty1 ty2
             | SOME opr => decide_ty ty1 (decide_ty ty2 (op_type opr)) in
      [(MAP2 decide_ty tt te, ty, IS_SOME oe, op)]) ∧
  (scan_expr ts loc [Let xs x] =
    let ys = scan_expr ts loc xs in
    let tt = MAP (FST o SND) ys in
    let tr = (dtcase LAST1 ys of SOME c => FST c | NONE => ts) in
    let (tu, ty, _, op) = HD (scan_expr (tt ++ tr) loc [x]) in
      [(DROP (LENGTH ys) tu, ty, F, op)]) ∧
  (scan_expr ts loc [Raise x] = [(ts, Any, F, NONE)]) ∧
  (scan_expr ts loc [Tick x] = scan_expr ts loc [x]) ∧
  (scan_expr ts loc [Call t d xs h] = [(ts, Any, F, NONE)]) ∧
  (scan_expr ts loc [Op op xs] =
    let opr = from_op op in
    let opt = op_type opr in
      dtcase opr of
        Noop => (* Constants? *)
          if arg_ty op = Int then
            dtcase get_bin_args (Op op xs) of
              NONE =>
                if is_const op then
                  [(ts, Int, F, NONE)]
                else
                  [(ts, Any, F, NONE)]
            | SOME (x, y) =>
                if ~is_const op then
                  [(update_context Int ts x y, Any, F, NONE)]
                else
                  [(ts, Any, F, NONE)]
          else if op = Cons 0 /\ xs = [] then (* list nil *)
            [(ts, List, F, NONE)]
          else
            [(ts, Any, F, NONE)]
      | _ => (* Things we can optimize *)
          if IS_SOME (check_op ts opr loc (Op op xs)) then
            [(ts, opt, F, SOME opr)]
          else if term_ok ts opt (Op op xs) then
            dtcase get_bin_args (Op op xs) of
              NONE => [(ts, Any, F, NONE)]
            | SOME (x, y) =>
                [(update_context opt ts x y, opt, F, NONE)]
          else
            [(ts, Any, F, NONE)])`
    (WF_REL_TAC `measure (exp2_size o SND o SND)`);

val push_call_def = Define `
  (push_call n op acc exp (SOME (ticks, dest, args, handler)) =
    Call ticks (SOME n) (args ++ [apply_op op (Var acc) exp]) handler) ∧
  (push_call _ _ _ _ _ = dummy)
  `;

val rewrite_def = Define `
  (rewrite loc next opr acc ts (Var n) = (F, Var n)) /\
  (rewrite loc next opr acc ts (If x1 x2 x3) =
    let t1 = FST (HD (scan_expr ts loc [x1])) in
    let (r2, y2) = rewrite loc next opr acc t1 x2 in
    let (r3, y3) = rewrite loc next opr acc t1 x3 in
    let z2 = if r2 then y2 else apply_op opr (Var acc) x2 in
    let z3 = if r3 then y3 else apply_op opr (Var acc) x3 in
      (r2 \/ r3, If x1 z2 z3)) /\
  (rewrite loc next opr acc ts (Let xs x) =
    let ys = scan_expr ts loc xs in
    let tt = MAP (FST o SND) ys in
    let tr = dtcase LAST1 ys of NONE => ts | SOME c => FST c in
    let (r, y) = rewrite loc next opr (acc + LENGTH xs) (tt ++ tr) x in
      (r, Let xs y)) /\
  (rewrite loc next opr acc ts (Tick x) =
    let (r, y) = rewrite loc next opr acc ts x in
      (r, Tick y)) /\
  (rewrite loc next opr acc ts exp =
    dtcase check_op ts opr loc exp of
      NONE => (F, apply_op opr (Var acc) exp)
    | SOME exp =>
        dtcase opbinargs opr exp of
          NONE => (F, apply_op opr (Var acc) exp)
        | SOME (xs, f) => (T, push_call next opr acc xs (args_from f)))`

Theorem rewrite_PMATCH:
   !loc next opr acc ts expr.
     rewrite loc next opr acc ts expr =
       case expr of
         Var n => (F, Var n)
       | If x1 x2 x3 =>
           let t1 = FST (HD (scan_expr ts loc [x1])) in
           let (r2, y2) = rewrite loc next opr acc t1 x2 in
           let (r3, y3) = rewrite loc next opr acc t1 x3 in
           let z2 = if r2 then y2 else apply_op opr (Var acc) x2 in
           let z3 = if r3 then y3 else apply_op opr (Var acc) x3 in
             (r2 \/ r3, If x1 z2 z3)
       | Let xs x =>
           let ys = scan_expr ts loc xs in
           let tt = MAP (FST o SND) ys in
           let tr = dtcase LAST1 ys of NONE => ts | SOME c => FST c in
           let (r, y) = rewrite loc next opr (acc + LENGTH xs) (tt ++ tr) x in
             (r, Let xs y)
       | Tick x =>
           let (r, y) = rewrite loc next opr acc ts x in (r, Tick y)
       | _ =>
           dtcase check_op ts opr loc expr of
             NONE => (F, apply_op opr (Var acc) expr)
           | SOME exp =>
             dtcase opbinargs opr exp of
               NONE => (F, apply_op opr (Var acc) exp)
             | SOME (xs, f) => (T, push_call next opr acc xs (args_from f))
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ recInduct (theorem "rewrite_ind") \\ rw [rewrite_def]
QED

(* --- Top-level expression check --- *)

val has_rec_def = tDefine "has_rec" `
  (has_rec loc [] = F) /\
  (has_rec loc (x::y::xs) =
    if has_rec loc [x] then T
    else has_rec loc (y::xs)) /\
  (has_rec loc [If x1 x2 x3] =
    if has_rec loc [x2] then T
    else has_rec loc [x3]) /\
  (has_rec loc [Let xs x] = has_rec loc [x]) /\
  (has_rec loc [Tick x] = has_rec loc [x]) /\
  (has_rec loc [Op op xs] =
    if EXISTS (is_rec loc) xs then T
    else has_rec loc xs) /\
  (has_rec loc [x] = F)`
  (WF_REL_TAC `measure (exp2_size o SND)`);

val has_rec1_def = Define `has_rec1 loc x = has_rec loc [x]`;

val test1_tm = ``Let [] (Call 0 (SOME 0) [] NONE)``
Theorem has_rec_test1:
   has_rec1 0 ^test1_tm <=> F
Proof
EVAL_TAC
QED

val test2_tm = ``Op Add [Call 0 (SOME 0) [] NONE; Var 0]``
Theorem has_rec_test2:
   has_rec1 0 ^test2_tm <=> T
Proof
EVAL_TAC
QED

val check_exp_def = Define `
  check_exp loc arity exp =
    if ~has_rec1 loc exp then NONE else
      let context = REPLICATE arity Any in
        dtcase scan_expr context loc [exp] of
          [] => NONE
        | (ts,ty,r,opr)::_ =>
            dtcase opr of
              NONE => NONE
            | SOME op =>
                if ty <> op_type op then NONE else opr`;

val let_wrap_def = Define `
  let_wrap arity id exp =
    Let ((GENLIST (λi. Var i) arity) ++ [id]) exp`;

val mk_aux_call_def = Define `
  mk_aux_call loc arity id =
    Call 0 (SOME loc) (id :: GENLIST (λi. Var i) arity) NONE`;

val compile_exp_def = Define `
  compile_exp loc next arity exp =
    dtcase check_exp loc arity exp of
      NONE => NONE
    | SOME op =>
      let context = REPLICATE arity Any in
      let (r, opt) = rewrite loc next op arity context exp in
      let aux      = let_wrap arity (id_from_op op) opt in
        SOME (aux, opt)`;

val compile_prog_def = Define `
  (compile_prog next [] = (next, [])) ∧
  (compile_prog next ((loc, arity, exp)::xs) =
    dtcase compile_exp loc next arity exp of
    | NONE =>
        let (n, ys) = compile_prog next xs in
          (n, (loc, arity, exp)::ys)
    | SOME (exp_aux, exp_opt) =>
        let (n, ys) = compile_prog (next + bvl_to_bvi_namespaces) xs in
        (n, (loc, arity, exp_aux)::(next, arity + 1, exp_opt)::ys))
  `;

Theorem scan_expr_not_nil[simp]:
   !x. scan_expr ts loc [x] <> []
Proof
  Induct \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs []
QED

Theorem LENGTH_scan_expr[simp]:
   ∀ts loc xs. LENGTH (scan_expr ts loc xs) = LENGTH xs
Proof
  recInduct (theorem"scan_expr_ind") \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs []
QED

Theorem scan_expr_SING[simp]:
   [HD (scan_expr ts loc [x])] = scan_expr ts loc [x]
Proof
  `LENGTH (scan_expr ts loc [x]) = LENGTH [x]` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []
QED

Theorem scan_expr_HD_SING[simp]:
   HD (scan_expr ts loc [x]) = y ⇔ scan_expr ts loc [x] = [y]
Proof
  `LENGTH (scan_expr ts loc [x]) = LENGTH [x]` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []
QED

Theorem check_exp_SOME_simp[simp]:
   check_exp loc arity exp = SOME op <=>
     ?ts ty r.
       has_rec1 loc exp /\
       scan_expr (REPLICATE arity Any) loc
         [exp] = [(ts,ty,r,SOME op)] /\
       ty = op_type op
Proof
  simp [check_exp_def]
  \\ `LENGTH (scan_expr (REPLICATE arity Any) loc [exp]) = LENGTH [exp]` by fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ PairCases_on `h` \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ metis_tac []
QED

(* --- Test rewriting --- *)

val fac_tm = ``
  Let [Op LessEq [Var 0; Op (Const 1) []]]
    (If (Var 0)
       (Op (Const 1) [])
       (Let [Op Sub [Op (Const 1) []; Var 1]]
         (Op Mult [Var 2; Call 0 (SOME 0) [Var 0] NONE])))``

val opt_tm = ``
  Let [Op LessEq [Var 0; Op (Const 1) []]]
     (If (Var 0) (Op Mult [Var 2; Op (Const 1) []])
        (Let [Op Sub [Op (Const 1) []; Var 1]]
           (Call 0 (SOME 1) [Var 0; Op Mult [Var 3; Var 2]]
              NONE)))``
val aux_tm = ``Let [Var 0; Op (Const 1) []] ^opt_tm``

Theorem fac_check_exp:
   check_exp 0 1 ^fac_tm = SOME Times
Proof
EVAL_TAC
QED

Theorem fac_compile_exp:
   compile_exp 0 1 1 ^fac_tm = SOME (^aux_tm, ^opt_tm)
Proof
EVAL_TAC
QED

val rev_tm = ``
  Let [Op (Const 0) []]
    (If (Op (TagLenEq 0 0) [Var 1])
        (Op (Cons 0) [])
        (Let [Op El [Op (Const 0) []; Var 1]]
          (Let [Op El [Op (Const 1) []; Var 2]]
            (Op ListAppend
              [Op (Cons 0) [Op (Cons 0) []; Var 1];
               Call 0 (SOME 444) [Var 0] NONE]))))``

val opt_tm = ``
  Let [Op (Const 0) []]
    (If (Op (TagLenEq 0 0) [Var 1])
        (Op ListAppend [Var 2; Op (Cons 0) []])
        (Let [Op El [Op (Const 0) []; Var 1]]
          (Let [Op El [Op (Const 1) []; Var 2]]
            (Call 0 (SOME 445)
              [Var 0;
               Op ListAppend [Var 4; Op (Cons 0) [Op (Cons 0) []; Var 1]]]
              NONE))))``

val aux_tm = ``Let [Var 0; Op (Cons 0) []] ^opt_tm``

Theorem rev_check_exp:
   check_exp 444 1 ^rev_tm = SOME Append
Proof
EVAL_TAC
QED

Theorem rev_compile_exp:
   compile_exp 444 445 1 ^rev_tm = SOME (^aux_tm, ^opt_tm)
Proof
EVAL_TAC
QED

val _ = export_theory();
