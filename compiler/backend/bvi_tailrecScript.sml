open preamble bviTheory backend_commonTheory;

(* TODO

   - When scan_expr returns an operation, the type it returns should match this
     operation. scan_expr may need some tweaks to ensure that this is always the
     case.

   - If rewrite succeeds for an operation and an expression, then scan_expr
     should succeed for the same combination.

   - It does not really work to run comml as-is; it changes order of evaluation
     and needs all expressions 'to the left' of the first function call to pass
     term_ok.

   - The update_context thing is incredibly annoying to work with (in
     particular, proving that the ty_rel relation holds also for the result).
     It might help to just figure out and prove the invariants.
*)

val _ = new_theory "bvi_tailrec";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();

val dummy_def = Define `dummy = bvi$Var 1234567890`;

val MEM_exp_size_imp = Q.store_thm ("MEM_exp_size_imp",
  `∀xs a. MEM a xs ⇒ bvi$exp_size a < exp2_size xs`,
  Induct \\ rw [bviTheory.exp_size_def] \\ res_tac \\ fs []);

(* TODO defined in bviSemTheory, should be moved to bviTheory?
   On the other hand: its use here is temporary.
*)
val small_int_def = Define `
  small_int (i:int) <=> -268435457 <= i /\ i <= 268435457`;

val is_rec_def = Define `
  (is_rec name (bvi$Call _ d _ NONE) ⇔ d = SOME name) ∧
  (is_rec _    _                     ⇔ F)
  `;

val is_rec_PMATCH = Q.store_thm ("is_rec_PMATCH",
  `!expr. is_rec name expr =
    case expr of
      Call _ d _ NONE => d = SOME name
    | _               => F`,
  Cases \\ rw [is_rec_def]
  \\ rename1 `Call _ _ _ hdl`
  \\ Cases_on `hdl` \\ fs [is_rec_def]);

val is_const_def = Define `
  (is_const (Const i) <=> small_int i) /\
  (is_const _         <=> F)`;

val is_const_PMATCH = Q.store_thm ("is_const_PMATCH",
  `!op. is_const op =
    case op of
      Const i => small_int i
    | _       => F`,
  Cases \\ rw [is_const_def]);

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

val from_op_PMATCH = Q.store_thm ("from_op_PMATCH",
  `!op.
    from_op op =
      case op of
        Add        => Plus
      | Mult       => Times
      | ListAppend => Append
      | _          => Noop`,
  Cases \\ rw [from_op_def]);

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

val op_eq_PMATCH = Q.store_thm ("op_eq_PMATCH",
  `!a expr.
     op_eq a expr =
       case expr of
         Op op xs =>
           (case a of
             Plus   => op = Add
           | Times  => op = Mult
           | Append => op = ListAppend
           | _      => F)
       | _ => F`,
  Cases \\ Cases \\ rw [op_eq_def]);

val op_eq_to_op = Q.store_thm ("op_eq_to_op[simp]",
  `∀iop op xs.
      op_eq iop (Op op xs)
      ⇔
      op = to_op iop ∧ iop ≠ Noop`,
  Cases \\ Cases \\ fs [op_eq_def, to_op_def]);

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

val index_of_PMATCH = Q.store_thm ("index_of_PMATCH",
  `!expr.
     index_of expr =
       case expr of
         Var i => SOME i
       | _     => NONE`,
  Cases \\ rw [index_of_def]);

val args_from_def = Define `
  (args_from (bvi$Call t (SOME d) as hdl) = SOME (t, d, as, hdl)) ∧
  (args_from _                            = NONE)
  `;

val args_from_PMATCH = Q.store_thm ("args_from_PMATCH",
  `!expr.
     args_from expr =
       case expr of
         Call t (SOME d) as hdl => SOME (t,d,as,hdl)
       | _                      => NONE`,
  Cases \\ rw [args_from_def]
  \\ rename1 `Call _ nm _ _`
  \\ Cases_on `nm` \\ rw [args_from_def]);

val get_bin_args_def = Define `
  get_bin_args op =
    dtcase op of
    | bvi$Op _ [e1; e2] => SOME (e1, e2)
    | _ => NONE`;

val get_bin_args_PMATCH = Q.store_thm ("get_bin_args_PMATCH",
  `!op.
     get_bin_args op =
       case op of
         Op _ [e1; e2] => SOME (e1,e2)
       | _             => NONE`,
  Cases \\ rw [get_bin_args_def]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []);

val exp_size_get_bin_args = Q.store_thm ("exp_size_get_bin_args",
  `∀x x1 x2.
     get_bin_args x = SOME (x1, x2) ⇒
       exp_size x1 + exp_size x2 < exp_size x`,
  Induct
  \\ rw [get_bin_args_def, exp_size_def]
  \\ every_case_tac
  \\ fs [exp_size_def]);

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

val is_arith_PMATCH = Q.store_thm("is_arith_PMATCH",
  `!op.
     is_arith op =
       case op of
         Add  => T
       | Sub  => T
       | Mult => T
       | _    => F`,
  Cases \\ rw [is_arith_def]);

val is_rel_def = Define `
  is_rel op =
    dtcase op of
      Less      => T
    | LessEq    => T
    | Greater   => T
    | GreaterEq => T
    | _         => F`;

val is_rel_PMATCH = Q.store_thm("is_rel_PMATCH",
  `!op.
     is_rel op =
       case op of
         Less      => T
       | LessEq    => T
       | Greater   => T
       | GreaterEq => T
       | _         => F`,
  Cases \\ rw [is_rel_def]);

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

val is_op_thms = Q.store_thm("is_op_thms",
  `~is_arith (Cons 0) /\ ~is_arith ListAppend /\
   ~is_rel (Cons 0) /\ ~is_rel ListAppend /\
   (!op. op <> ListAppend /\ is_arith op <=> is_arith op) /\
   (!op. op <> ListAppend /\ ~is_arith op /\ is_rel op <=> is_rel op) /\
   (!op. ~is_arith op /\ ~is_rel op /\ op = Cons 0 <=> op = Cons 0) /\
   (!op. op <> ListAppend /\ op = Cons 0 <=> op = Cons 0)`,
  rw [is_arith_def, is_rel_def] \\ fs []
  \\ Cases_on `op` \\ fs []);

val term_ok_any_ind = save_thm ("term_ok_any_ind",
  theorem "term_ok_any_ind" |> SIMP_RULE (srw_ss()) [is_op_thms]);

(* TODO the translator does not accept this with the induction theorem
   above (yet):

val term_ok_any_PMATCH = Q.store_thm("term_ok_any_PMATCH",
  `term_ok_any ts list expr =
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
     | _ => F`,
  Cases_on `expr` \\ once_rewrite_tac [term_ok_any_def] \\ fs []);
*)
val term_ok_def = Define `
  term_ok ts ty expr =
    dtcase ty of
      Any  => term_ok_any ts F expr
    | Int  => term_ok_int ts expr
    | List => term_ok_any ts T expr`;

(* --- Right-associate all targeted operations --- *)

val rotate_def = tDefine "rotate" `
  rotate opr exp =
    dtcase opbinargs opr exp of
      NONE => exp
    | SOME (a, c) =>
        dtcase opbinargs opr a of
          NONE => exp
        | SOME (a, b) =>
            rotate opr (apply_op opr a (apply_op opr b c))`
  (WF_REL_TAC `measure (\(opr,x).
    dtcase opbinargs opr x of
      NONE => exp_size x
    | SOME (a, c) => exp_size a)`
  \\ rw [opbinargs_def, apply_op_def, get_bin_args_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ Cases_on `opr` \\ fs [to_op_def, op_eq_def]
  \\ fs [bviTheory.exp_size_def]);

val rotate_exp_size = Q.store_thm("rotate_exp_size",
  `!opr exp. exp_size exp = exp_size (rotate opr exp)`,
  recInduct (theorem "rotate_ind") \\ rw []
  \\ once_rewrite_tac [rotate_def]
  \\ CASE_TAC \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ CASE_TAC \\ fs []
  \\ fs [apply_op_def, opbinargs_def, get_bin_args_def]
  \\ every_case_tac \\ fs [] \\ rveq
  \\ Cases_on `opr`
  \\ fs [to_op_def, bviTheory.exp_size_def, closLangTheory.op_size_def]);

val do_assocr_def = tDefine "do_assocr" `
  do_assocr opr exp =
    dtcase opbinargs opr exp of
      NONE => exp
    | SOME _ =>
        dtcase opbinargs opr (rotate opr exp) of
          NONE => exp
        | SOME (l, r) =>
            apply_op opr l (do_assocr opr r)`
  (WF_REL_TAC `measure (exp_size o SND)`
   \\ rw [opbinargs_def, get_bin_args_def]
   \\ every_case_tac \\ fs [] \\ rw []
   \\ qmatch_asmsub_abbrev_tac `rotate _ exp`
   \\ `exp_size exp = exp_size (rotate opr exp)` by fs [rotate_exp_size]
   \\ unabbrev_all_tac
   \\ rfs []
   \\ fs [bviTheory.exp_size_def])

val assocr_def = Define `
  (assocr (If x1 x2 x3) = If x1 (assocr x2) (assocr x3)) /\
  (assocr (Let xs x) = Let xs (assocr x)) /\
  (assocr (Tick x) = Tick (assocr x)) /\
  (assocr (Op op xs) =
    if ~(op = Add \/ op = Mult \/ op = ListAppend) then Op op xs
    else do_assocr (from_op op) (Op op xs)) /\
  (assocr exp = exp)`;

val assocr_PMATCH = Q.store_thm ("assocr_PMATCH",
  `!expr.
     assocr expr =
       case expr of
         If x1 x2 x3      => If x1 (assocr x2) (assocr x3)
       | Let xs x         => Let xs (assocr x)
       | Tick x           => Tick (assocr x)
       | Op Add xs        => do_assocr Plus expr
       | Op Mult xs       => do_assocr Times expr
       | Op ListAppend xs => do_assocr Append expr
       | _                => expr`,
  Induct \\ rw [assocr_def]
  \\ rename1 `from_op op`
  \\ Cases_on `op` \\ fs []);

(* Test do_assocr *)
val test_tm = ``
  apply_op Plus
    (apply_op Plus (Var 0)
      (apply_op Plus (apply_op Plus (Var 1) (Var 2)) (Var 3)))
    (apply_op Plus (apply_op Plus (Var 4) (Var 5)) (Var 6))``;

val succ_tm = ``
  apply_op Plus (Var 0) (apply_op Plus (Var 1) (apply_op Plus (Var 2)
    (apply_op Plus (Var 3)
    (apply_op Plus (Var 4) (apply_op Plus (Var 5) (Var 6))))))``;

val do_assocr_test = Q.store_thm ("do_assocr_test",
  `do_assocr Plus ^test_tm = ^succ_tm`, EVAL_TAC);

(* --- Do commutative shifts of recursive calls --- *)

(* Assumes that tree is rotated right *)
val do_comml_def = tDefine "do_comml" `
  do_comml ts loc opr exp =
    dtcase opbinargs opr exp of
      NONE => exp
    | SOME (l, r) =>
        if is_rec loc l then exp
        else if ~term_ok ts Int l then exp
        else if is_rec loc r then apply_op opr r l
        else
          dtcase opbinargs opr (do_comml ts loc opr r) of
            NONE => exp
          | SOME (r1, r2) =>
              if is_rec loc r1 then
                apply_op opr r1 (apply_op opr l r2)
              else exp`
  (WF_REL_TAC `measure (exp_size o SND o SND o SND)`
  \\ rw [opbinargs_def]
  \\ imp_res_tac exp_size_get_bin_args \\ fs []);

(* Test do_comml *)

val test_tm = ``
  apply_op Plus (Var 0) (apply_op Plus (Call 0 (SOME 0) [] NONE) (Var 1))``;

val succ_tm = ``
  apply_op Plus (Call 0 (SOME 0) [] NONE) (apply_op Plus (Var 0) (Var 1))``;

val do_comml_test1 = Q.store_thm("do_comml_test1",
  `do_comml [Int; Int] 0 Plus ^test_tm = ^succ_tm`, EVAL_TAC);

val test_tm = ``apply_op Times (Var 0) (Call 0 (SOME 0) [] NONE)``
val succ_tm = ``apply_op Times (Call 0 (SOME 0) [] NONE) (Var 0)``;
val do_comml_test2 = Q.store_thm("do_comml_test2",
  `do_comml [Int] 0 Times ^test_tm = ^succ_tm`, EVAL_TAC);

(* --- Simple tail checking before rewriting --- *)

(* Check if ok to lift xs into accumulator *)
val check_op_def = Define `
  check_op ts opr loc exp =
    dtcase opbinargs opr exp of
      NONE => F
    | SOME (f, xs) => is_rec loc f /\ term_ok ts (op_type opr) xs`;

(* --- Type analysis --- *)

val decide_ty_def = Define `
  (decide_ty Int  Int  = Int)  /\
  (decide_ty List List = List) /\
  (decide_ty _    _    = Any)`;

val decide_ty_PMATCH = Q.store_thm ("decide_ty_PMATCH",
  `!ty1 ty2.
     decide_ty ty1 ty2 =
       case (ty1,ty2) of
         (Int, Int)   => Int
       | (List, List) => List
       | _            => Any`,
  Cases \\ Cases \\ rw [decide_ty_def]);

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

val arg_ty_PMATCH = Q.store_thm ("arg_ty_PMATCH",
  `!op.
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
       | _          => Any`,
  Cases \\ rw [arg_ty_def]);

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

val op_ty_PMATCH = Q.store_thm ("op_ty_PMATCH",
  `!op.
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
       | _          => Any`,
  Cases \\ rw [op_ty_def]);

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
          else
            [(ts, Any, F, NONE)]
      | _ => (* Things we can optimize *)
          if check_op ts opr loc (Op op xs) then
            [(ts, opt, F, SOME opr)]
          else if term_ok ts opt (Op op xs) then
            dtcase get_bin_args (Op op xs) of
              NONE => [(ts, Any, F, NONE)]
            | SOME (x, y) =>
                [(update_context opt ts x y, opt, F, NONE)]
          else
            [(ts, Any, F, NONE)])`
    (WF_REL_TAC `measure (exp2_size o SND o SND)`);

(* Either comml gets type information from scan_expr, or do_comml is executed
   twice: inside scan_expr and inside rewrite. *)
val comml_def = Define `
  (comml ts loc (If x1 x2 x3) =
    let t1 = FST (HD (scan_expr ts loc [x1])) in
    let y2 = comml t1 loc x2 in
    let y3 = comml t1 loc x3 in
      If x1 y2 y3) /\
  (comml ts loc (Let xs x) =
    let ys = scan_expr ts loc xs in
    let tt = MAP (FST o SND) ys in
    let tr = (dtcase LAST1 ys of SOME c => FST c | NONE => ts) in
    let y  = comml (tt ++ tr) loc x in
      Let xs y) /\
  (comml ts loc (Tick x) = Tick (comml ts loc x)) /\
  (comml ts loc (Op op xs) =
    if ~(op = Add \/ op = Mult) then Op op xs
    else do_comml ts loc (from_op op) (Op op xs)) /\
  (comml ts loc exp = exp)`;

(* TODO The translator does not accept this (yet):

val comml_PMATCH = Q.store_thm ("comml_PMATCH",
  `!ts loc expr.
     comml ts loc expr =
       case expr of
         If x1 x2 x3 =>
           let t1 = FST (HD (scan_expr ts loc [x1])) in
           let y2 = comml t1 loc x2 in
           let y3 = comml t1 loc x3 in
             If x1 y2 y3
       | Let xs x =>
           let ys = scan_expr ts loc xs in
           let tt = MAP (FST o SND) ys in
           let tr = (case LAST1 ys of SOME c => FST c | NONE => ts) in
           let y  = comml (tt ++ tr) loc x in
             Let xs y
       | Tick x     => Tick (comml ts loc x)
       | Op Add xs  => do_comml ts loc Plus expr
       | Op Mult xs => do_comml ts loc Times expr
       | _          => expr`,
  recInduct (theorem "comml_ind") \\ rw [comml_def]
  >- (Cases_on `x` \\ fs [] \\ FULL_CASE_TAC \\ fs [])
  \\ Cases_on `op` \\ fs []);
*)

val push_call_def = Define `
  (push_call n op acc exp (SOME (ticks, dest, args, handler)) =
    Call ticks (SOME n) (args ++ [apply_op op exp (Var acc)]) handler) ∧
  (push_call _ _ _ _ _ = dummy)
  `;

val rewrite_def = Define `
  (rewrite loc next opr acc ts (Var n) = (F, Var n)) /\
  (rewrite loc next opr acc ts (If x1 x2 x3) =
    let t1 = FST (HD (scan_expr ts loc [x1])) in
    let (r2, y2) = rewrite loc next opr acc t1 x2 in
    let (r3, y3) = rewrite loc next opr acc t1 x3 in
    let z2 = if r2 then y2 else apply_op opr x2 (Var acc) in
    let z3 = if r3 then y3 else apply_op opr x3 (Var acc) in
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
    if ~check_op ts opr loc exp then (F, apply_op opr exp (Var acc)) else
      dtcase opbinargs opr exp of
        NONE => (F, apply_op opr exp (Var acc))
      | SOME (f, xs) => (T, push_call next opr acc xs (args_from f)))`

val rewrite_PMATCH = Q.store_thm ("rewrite_PMATCH",
  `!loc next opr acc ts expr.
     rewrite loc next opr acc ts expr =
       case expr of
         Var n => (F, Var n)
       | If x1 x2 x3 =>
           let t1 = FST (HD (scan_expr ts loc [x1])) in
           let (r2, y2) = rewrite loc next opr acc t1 x2 in
           let (r3, y3) = rewrite loc next opr acc t1 x3 in
           let z2 = if r2 then y2 else apply_op opr x2 (Var acc) in
           let z3 = if r3 then y3 else apply_op opr x3 (Var acc) in
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
           if ~check_op ts opr loc expr then
             (F, apply_op opr expr (Var acc))
           else
             dtcase opbinargs opr expr of
               NONE => (F, apply_op opr expr (Var acc))
             | SOME (f, xs) => (T, push_call next opr acc xs (args_from f))`,
  recInduct (theorem "rewrite_ind") \\ rw [rewrite_def]);

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
val has_rec_test1 = Q.store_thm("has_rec_test1",
  `has_rec1 0 ^test1_tm <=> F`, EVAL_TAC);

val test2_tm = ``Op Add [Call 0 (SOME 0) [] NONE; Var 0]``
val has_rec_test2 = Q.store_thm("has_rec_test2",
  `has_rec1 0 ^test2_tm <=> T`, EVAL_TAC);

val check_exp_def = Define `
  check_exp loc arity exp =
    if ~has_rec1 loc exp then NONE else
      let context = REPLICATE arity Any in
      let expa = assocr exp in
      let expc = comml context loc expa in
        dtcase scan_expr context loc [expc] of
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
      NONE    => NONE
    | SOME op =>
      let context  = REPLICATE arity Any in
      let expa = assocr exp in
      let expc = comml context loc expa in
      let (r, opt) = rewrite loc next op arity context expc in
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

val scan_expr_not_nil = Q.store_thm ("scan_expr_not_nil[simp]",
  `!x. scan_expr ts loc [x] <> []`,
  Induct \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs []);

val LENGTH_scan_expr = Q.store_thm ("LENGTH_scan_expr[simp]",
  `∀ts loc xs. LENGTH (scan_expr ts loc xs) = LENGTH xs`,
  recInduct (theorem"scan_expr_ind") \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs []);

val scan_expr_SING = Q.store_thm ("scan_expr_SING[simp]",
  `[HD (scan_expr ts loc [x])] = scan_expr ts loc [x]`,
  `LENGTH (scan_expr ts loc [x]) = LENGTH [x]` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []);

val scan_expr_HD_SING = Q.store_thm ("scan_expr_HD_SING[simp]",
  `HD (scan_expr ts loc [x]) = y ⇔ scan_expr ts loc [x] = [y]`,
  `LENGTH (scan_expr ts loc [x]) = LENGTH [x]` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []);

val check_exp_SOME_simp = Q.store_thm ("check_exp_SOME_simp[simp]",
  `check_exp loc arity exp = SOME op <=>
     ?ts ty r.
       has_rec1 loc exp /\
       scan_expr (REPLICATE arity Any) loc
         [comml (REPLICATE arity Any) loc (assocr exp)] = [(ts,ty,r,SOME op)] /\
       ty = op_type op`,
  simp [check_exp_def]
  \\ `LENGTH (scan_expr (REPLICATE arity Any) loc
        [comml (REPLICATE arity Any) loc (assocr exp)]) = LENGTH [exp]` by fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ PairCases_on `h` \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ metis_tac []);

(* --- Test rewriting --- *)

val fac_tm = ``
  Let [Op LessEq [Var 0; Op (Const 1) []]]
    (If (Var 0)
       (Op (Const 1) [])
       (Let [Op Sub [Var 1; Op (Const 1) []]]
         (Op Mult [Var 2; Call 0 (SOME 0) [Var 0] NONE])))``

val opt_tm = ``
  Let [Op LessEq [Var 0; Op (Const 1) []]]
     (If (Var 0) (Op Mult [Op (Const 1) []; Var 2])
        (Let [Op Sub [Var 1; Op (Const 1) []]]
           (Call 0 (SOME 1) [Var 0; Op Mult [Var 2; Var 3]]
              NONE)))``
val aux_tm = ``Let [Var 0; Op (Const 1) []] ^opt_tm``

val fac_check_exp = Q.store_thm("fac_check_exp",
  `check_exp 0 1 ^fac_tm = SOME Times`, EVAL_TAC);

val fac_compile_exp = Q.store_thm("fac_compile_exp",
  `compile_exp 0 1 1 ^fac_tm = SOME (^aux_tm, ^opt_tm)`, EVAL_TAC);

val _ = export_theory();

