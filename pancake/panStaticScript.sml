(*
  Static checking for Pancake.

  Scope checks:
  - Errors:
    - Undefined/out-of-scope functions
    - Undefined/out-of-scope variables
    - Redefined functions
  - Warnings:
    - Redefined variables

  General checks:
  - Errors:
    - Main function parameters
    - Exported main function
    - Exported function with >4 arguments
    - Missing function exit (return, tail call, etc)
    - Loop exit outside loop (break, continue)
    - Function parameter names not distinct
    - Incorrect number of Op arguments (impossible from parser)
  - Warnings:
    - Unreachable statements (after function exit, after loop exit)
      - Note: To minimise output, subsequent warnings of this kind after the
        first guaranteed-unreachable line within a block are silenced. If an
        inner block occurs *before* this line, warnings within that block do not
        count towards this first. However, if an inner block occurs *after* this
        line, the line is recognised as the first for the inner block as well
    - Base-calculated address in shared memory operation
    - Non-base -calculated address in local memory operation

  Shape checks: TODO
*)
Theory panStatic
Libs
  preamble
Ancestors
  errorLogMonad panLang mlmap mlint mllist


val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "errorLog";


(* Error categories for printing *)
Datatype:
  staterr = ScopeErr mlstring
          | WarningErr mlstring
          | GenErr mlstring
          | ShapeErr mlstring
End

(*
  Return type of static_check_* functions:
    (retval, proper error) error # warning list
*)
Type static_result = ``:('a, staterr) error # staterr list``

(*
  Exp-level state for references to @base
  "Priority": `Based` > `NotTrusted` > `Trusted` > `NotBased`
    where an exp can never have a lower priority state to its components,
    ie. an exp containing a `NotTrusted` exp can never be `Trusted` or `NotBased`
*)
Datatype:
  based =
    Based | NotBased  (* warned as appropriate *)
  | Trusted           (* excempt from warning *)
  | NotTrusted        (* always warned *)
End

(* Exp-level state for field-granularity basedness *)
Datatype:
  shaped_based =
    WordB    based
  | StructB (shaped_based list)
End

(*
  Prog-level state for reachability
  Possible transitions are linear: `IsReach` -> `WarnReach` -> `NotReach`
    where `NotReach` only comes after a reachability warning
*)
Datatype:
  reachable =
    IsReach | NotReach  (* as named *)
  | WarnReach           (* "unreachable but has a pending warning" *)
End

(* Prog-level state for exit-ness of final statement *)
Datatype:
  last_stmt =
    RetLast | RaiseLast | TailLast  (* function exit *)
  | BreakLast | ContLast            (* loop exit *)
  | CondExitLast                    (* ambiguous exit (after conditionals) *)
  | InvisLast | OtherLast           (* non-exit *)
End

(* Type for function state *)
Datatype:
  func_info = <|
    ret_shape : shape                  (* shape of return value *)
  ; params    : (varname # shape) list (* parameter info *)
  |>
End

(* Type for local var state *)
Datatype:
  local_info = <|
    vsh_based : shaped_based (* shaped basedness of var *)
  |>
End

(* Type for global var state *)
Datatype:
  global_info = <|
    vshape : shape (* shape of var *)
  |>
End

Datatype:
  scope =
    FunScope  funname   (* in a function *)
  | DeclScope varname   (* in a global declaration *)
  | TopLevel
End

(* Record for current (per-func) context *)
Datatype:
  context = <|
    locals       : (varname, local_info ) map (* tracked var state *)
  ; globals      : (varname, global_info) map (* declared globals *)
  ; funcs        : (funname, func_info  ) map (* all function info *)
  ; scope        : scope                      (* current scope info *)
  ; in_loop      : bool                       (* loop status *)
  ; is_reachable : reachable                  (* reachability *)
  ; last         : last_stmt                  (* exit-ness of last statement *)
  ; loc          : mlstring                   (* location string *)
  |>
End

(* Record for static_check_exp returns *)
Datatype:
  exp_return = <|
    sh_based : shaped_based (* shaped basedness of exp *)
  |>
End

(* Record for static_check_exps returns *)
Datatype:
  exps_return = <|
    sh_baseds : shaped_based list (* shaped basedness of exps *)
  |>
End

(* Record for static_check_prog returns *)
Datatype:
  prog_return = <|
    exits_fun  : bool                       (* func exit status for all paths *)
  ; exits_loop : bool                       (* loop exit status for all paths *)
  ; last       : last_stmt                  (* new exit-ness of last statement *)
  ; var_delta  : (varname, local_info) map  (* change in var state *)
  ; curr_loc   : mlstring                   (* latest location string *)
  |>
End


(* Functions for `based` and `shaped_based` *)

(* Determine based-ness according to priority *)
Definition based_merge_def:
  based_merge x y =
    case (x,y) of
    | (Based, _) => Based
    | (_, Based) => Based
    | (NotTrusted, _) => NotTrusted
    | (_, NotTrusted) => NotTrusted
    | (Trusted, _) => Trusted
    | (_, Trusted) => Trusted
    | (NotBased, NotBased) => NotBased
End

(* #!TODO *)
Definition sh_based_merge_def:
  sh_based_merge x y =
    case (x, y) of
    | (WordB b, WordB b') => WordB $ based_merge b b'
    | (StructB sbs, StructB sbs') => StructB $ MAP2 sh_based_merge sbs sbs'
    | _ => ARB
Termination
  cheat
End

(* #!TODO *)
Definition sh_based_get_def:
  sh_based_get b One = WordB b /\
  sh_based_get b (Comb shs) = StructB $ MAP (sh_based_get b) shs
Termination
  cheat
End

(* #!TODO *)
Definition sh_based_set_def:
  sh_based_set b (WordB b') = WordB b /\
  sh_based_set b (StructB sbs) = StructB $ MAP (sh_based_set b) sbs
Termination
  cheat
End

(* Comparison for combining based-ness between If/While branches *)
Definition sh_based_branch_def:
  sh_based_branch x y = if x = y then x else sh_based_set NotTrusted x
End

(*
  Combine var state deltas of If/While branches
    where states are either combined between the two deltas (if in both) or with
    prior context (if in just one)
  Needs extension with extension of `local_info` type
*)
Definition branch_vbases_def:
  branch_vbases vctxt x y =
    let x' = mapWithKey (\k v. v with <| vsh_based :=
              (if ~(member k y) then
                case lookup vctxt k of
                | SOME v' => sh_based_branch v.vsh_based v'.vsh_based
                | NONE => sh_based_set NotTrusted v.vsh_based
              else v.vsh_based) |>) x;
        y' = mlmap$mapWithKey (\k v. v with <| vsh_based :=
              (if ~(member k x) then
                case lookup vctxt k of
                | SOME v' => sh_based_branch v.vsh_based v'.vsh_based
                | NONE => sh_based_set NotTrusted v.vsh_based
              else v.vsh_based) |>) y;
    in mlmap$unionWith (\vx vy. vx with <| vsh_based := sh_based_branch vx.vsh_based vy.vsh_based |>) x' y'
End

(* Combine var state deltas of Seq progs *)
Definition seq_vbases_def:
  seq_vbases x y = union y x
End

(* #!TODO *)
Definition sh_based_has_shape_def:
  sh_based_has_shape sh sb =
    case (sh, sb) of
    | (One, WordB b) => T
    | (Comb shs, StructB sbs) => ((LENGTH shs = LENGTH sbs) /\ EVERY2 (\x y. sh_based_has_shape x y) shs sbs)
    | _ => F
Termination
  cheat
End

(* #!TODO *)
Definition sh_based_eq_shapes_def:
  sh_based_eq_shapes sb sh =
    case (sb, sh) of
    | (WordB b, WordB b') => T
    | (StructB (sbs), StructB (sbs')) => ((LENGTH sbs = LENGTH sbs') /\ EVERY2 (\x y. sh_based_eq_shapes x y) sbs sbs')
    | _ => F
Termination
  cheat
End

(* Get shape at a certain struct index *)
Definition index_sh_based_def:
  index_sh_based i (WordB b) = NONE ∧
  index_sh_based i (StructB sbs) = LLOOKUP sbs i
End


(* Functions for `last_stmt` and `reachable` *)

(*
  Get string name for statement exit-ness
  USED FOR PRINTING ASSOCIATED WARNINGS ONLY
*)
Definition last_to_str_def:
  last_to_str l =
    case l of
    | RetLast      => implode "return"
    | RaiseLast    => implode "raise"
    | TailLast     => implode "tail call"
    | BreakLast    => implode "break"
    | ContLast     => implode "continue"
    | CondExitLast => implode "exiting conditional"
    | _            => implode ""
End

(*
  Determine next reachability state for prog sequences based on current state
    and exit-ness
  Handles `IsReach` -> `WarnReach` transition
*)
Definition next_is_reachable_def:
  next_is_reachable r x =
    case r of
    | IsReach => if ~(x = InvisLast \/ x = OtherLast) then WarnReach else IsReach
    | _ => r
End

(* Determine whether reachability has decreased *)
Definition next_now_unreachable_def:
  next_now_unreachable r r' = (r = IsReach /\ ~(r' = IsReach))
End

(*
  Determine whether a prog that can trigger a reachability warning is reached,
    and return last exit-ness and update context if so
  Handles `WarnReach` -> `NotReach` transition
*)
Definition reached_warnable_def:
  reached_warnable s ctxt =
    case s of
    | Seq p1 p2   => (NONE, ctxt)
    | Tick        => (NONE, ctxt)
    | Annot s1 s2 => (NONE, ctxt)
    | _           =>
      if ctxt.is_reachable = WarnReach then
        (SOME ctxt.last, ctxt with is_reachable := NotReach)
      else (NONE, ctxt)
End

(*
  Determine exit-ness of branches, based on whether a definite func or loop exit
    occurred
*)
Definition branch_last_stmt_def:
  branch_last_stmt double_ret double_loop_exit =
    if (double_ret \/ double_loop_exit) then CondExitLast else OtherLast
End

(* Determine exit-ness of Seq'd progs by ignoring invisible exit-ness *)
Definition seq_last_stmt_def:
  seq_last_stmt x y = if y = InvisLast then x else y
End


(* Error message helpers *)

(* Get description of current scope *)
Definition get_scope_desc_def:
  get_scope_desc scope =
    case scope of
    | FunScope fname =>
        concat [strlit "function "; fname]
    | DeclScope vname =>
        concat [strlit "initialisation of global variable "; vname]
    | TopLevel =>
        strlit "top-level declaration"
End

(*
  Get message for out of scope identifiers
  is_var: variable vs function
*)
Definition get_scope_msg_def:
  get_scope_msg is_var loc id scope =
    let id_type = if is_var then strlit "variable " else strlit "function " in
    concat [loc; id_type; id;
      strlit " is not in scope in ";
      get_scope_desc scope; strlit "\n"]
End

(*
  Get message for redefined identifiers
  is_var: variable vs function
*)
Definition get_redec_msg_def:
  get_redec_msg is_var loc id scope =
    let id_type = if is_var then strlit "variable " else strlit "function " in
    concat [loc; id_type; id;
      strlit " is redeclared in"; get_scope_desc scope; strlit "\n"]
End

(*
  Get message for memory op addresses
  is_local: local vs shared
  is_load: load vs store
  is_untrust: NotTrusted vs other
*)
Definition get_memop_msg_def:
  get_memop_msg is_local is_load is_untrust loc scope =
    let mem_type = if is_local then strlit "local " else strlit "shared " in
    let op_type  = if is_load  then strlit "load "  else strlit "store "  in
    let issue = case (is_local, is_untrust) of
      | (F, F) => strlit "is "
      | (F, T) => strlit "may be "
      | (T, F) => strlit "is not "
      | (T, T) => strlit "may not be " in
    concat [loc; mem_type; op_type;
      strlit "address "; issue; strlit "calculated from base in ";
      get_scope_desc scope; strlit "\n"]
End

(*
  Get message for op argument number
  is_exact: exactly vs at least
*)
Definition get_oparg_msg_def:
  get_oparg_msg is_exact n_expected n_given loc op scope =
    let issue = if is_exact then strlit " only accepts " else strlit " requires at least " in
    concat
      [loc; strlit "operation "; op;
        issue; n_expected; strlit " operands, ";
        n_given; strlit " provided in ";
        get_scope_desc scope; strlit "\n"]
End

(* Get message for unreachable statement *)
Definition get_unreach_msg_def:
  get_unreach_msg loc last scope =
    concat
      [loc;
        strlit "unreachable statement(s) after "; last;
        strlit " in " ; get_scope_desc scope; strlit "\n"]
End

(*
  Get message for rogue loop exit
  is_break: break vs continue
*)
Definition get_rogue_msg_def:
  get_rogue_msg is_break loc scope =
    let stmt = if is_break then strlit "break " else strlit "continue " in
    concat
      [loc; stmt;
        strlit "statement outside loop in ";
        get_scope_desc scope; strlit "\n"]
End


(* Misc functions *)

(* Find the first element in a sorted list that is repeated *)
Definition first_repeat_def:
  first_repeat xs =
    case xs of
    | (x1::x2::xs) =>
        if x1 = x2
          then SOME x1
        else first_repeat $ x2::xs
    | _ => NONE
End

(* Get string name for binary ops *)
Definition binop_to_str_def:
  binop_to_str op =
    case op of
    | Add => implode "Add"
    | Sub => implode "Sub"
    | And => implode "And"
    | Or  => implode "Or"
    | Xor => implode "Xor"
End

(* Get string name for Pancake ops *)
Definition panop_to_str_def:
  panop_to_str op =
    case op of
    | Mul => implode "Mul"
End


(* Static check helpers *)

(* Check for out of scope func *)
Definition scope_check_fun_name_def:
  scope_check_fun_name ctxt fname =
    case lookup ctxt.funcs fname of
    | NONE => error (ScopeErr $ get_scope_msg F ctxt.loc fname ctxt.scope)
    | SOME f => return f
End

(* Check for out of scope global *)
Definition scope_check_global_var_def:
  scope_check_global_var ctxt vname =
    case lookup ctxt.globals vname of
    | NONE => error (ScopeErr $ get_scope_msg T ctxt.loc vname ctxt.scope)
    | SOME v => return v
End

(* Check for out of scope local *)
Definition scope_check_local_var_def:
  scope_check_local_var ctxt vname =
    case lookup ctxt.locals vname of
    | NONE => error (ScopeErr $ get_scope_msg T ctxt.loc vname ctxt.scope)
    | SOME v => return v
End

(* Check for redeclared variable *)
Definition check_redec_var_def:
  check_redec_var ctxt vname =
    case (lookup ctxt.locals vname,lookup ctxt.globals vname) of
    |  (NONE,NONE) => return ()
    |  _ => log (WarningErr $ get_redec_msg T ctxt.loc vname ctxt.scope)
End

(* Check for arg number and shape *)
Definition check_func_args_def:
  check_func_args ctxt fname params sh_baseds =
    case (params, sh_baseds) of
    | ((p,s)::ps, sb::sbs) =>
      if ~(sh_based_has_shape s sb)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "value for argument "; p;
           strlit " given to function "; fname;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else check_func_args ctxt fname ps sbs
    | ((p,s)::ps, []) => error (GenErr $ concat
          [ctxt.loc; strlit "argument "; p;
           strlit " for call to function "; fname;
           strlit " is missing in ";
           get_scope_desc ctxt.scope; strlit "\n"])
    | ([], sb::sbs) => error (GenErr $ concat
          [ctxt.loc; strlit "extra arguments given to function "; fname;
           strlit " in ";
           get_scope_desc ctxt.scope; strlit "\n"])
    | ([], []) => return ()
End


(* Main static checking functions *)

(*
  static_check_exp returns:
    (exp info (:exp_return)) static_result
  static_check_exps returns:
    (exps info (:exps_return)) static_result
*)
Definition static_check_exp_def:
  static_check_exp ctxt (Const c) =
    (* return exp info *)
    return <| sh_based := WordB NotBased |> ∧
  static_check_exp ctxt (Var Local vname) =
    do
      (* check for out of scope var *)
      vinf <- scope_check_local_var ctxt vname;
      (* return stored info *)
      return <| sh_based := vinf.vsh_based |>
    od ∧
  static_check_exp ctxt (Var Global vname) =
    do
      (* check for out of scope var *)
      vinf <- scope_check_global_var ctxt vname;
      (* return exp info with stored shape *)
      return <| sh_based := sh_based_get Trusted vinf.vshape |>
    od ∧
  static_check_exp ctxt (Struct es) =
    do
      (* check struct field exps *)
      esret <- static_check_exps ctxt es;
      (* return exp info with found shape *)
      return <| sh_based := StructB esret.sh_baseds |>
    od ∧
  static_check_exp ctxt (Field index e) =
    do
      (* check struct exp *)
      eret <- static_check_exp ctxt e;
      case index_sh_based index eret.sh_based of
      | NONE => error (ShapeErr $ concat
        [ctxt.loc; strlit "expression has no field at index "; num_to_str index;
          get_scope_desc ctxt.scope; strlit "\n"])
      (* return exp info with found shape *)
      | SOME sb => return <| sh_based := sb |>
    od ∧
  static_check_exp ctxt (Load shape addr) =
    do
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "load address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return exp info *)
      return <| sh_based := sh_based_get Trusted shape |>
    od ∧
  static_check_exp ctxt (Load32 addr) =
    do
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "load address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return exp info *)
      return <| sh_based := WordB Trusted |>
    od ∧
  static_check_exp ctxt (LoadByte addr) =
    do
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "load address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return exp info *)
      return <| sh_based := WordB Trusted |>
    od ∧
  static_check_exp ctxt (Op bop es) =
    do
      (* check num of op args *)
      nargs <<- LENGTH es;
      case bop of
      | Sub  => if ~(nargs = 2)
                  then error (GenErr $ get_oparg_msg T (strlit "2")
                    (num_to_str nargs) ctxt.loc (binop_to_str bop) ctxt.scope)
                else return ()
      | _    => if nargs < 2
                  then error (GenErr $ get_oparg_msg F (strlit "2")
                    (num_to_str nargs) ctxt.loc (binop_to_str bop) ctxt.scope)
                else return ();
      (* check op args *)
      esret <- static_check_exps ctxt es;
      (* check arg shapes *)
      if ~(EVERY (sh_based_has_shape One) esret.sh_baseds)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "operation "; binop_to_str bop;
           strlit " given a non-word operand in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return exp info with combined basedness of args *)
      return <| sh_based := FOLDL sh_based_merge (WordB NotBased) esret.sh_baseds |>
    od ∧
  static_check_exp ctxt (Panop pop es) =
    do
      (* check num of op args *)
      nargs <<- LENGTH es;
      case pop of
      | Mul  => if ~(nargs = 2)
                  then error (GenErr $ get_oparg_msg T (strlit "2")
                    (num_to_str nargs) ctxt.loc (panop_to_str pop) ctxt.scope)
                else return ();
      (* check op args *)
      esret <- static_check_exps ctxt es;
      (* check arg shapes *)
      if ~(EVERY (sh_based_has_shape One) esret.sh_baseds)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "operation "; panop_to_str pop;
           strlit " given a non-word operand in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return exp info with combined basedness of args *)
      return <| sh_based := FOLDL sh_based_merge (WordB NotBased) esret.sh_baseds |>
    od ∧
  static_check_exp ctxt (Cmp cmp e1 e2) =
    do
      (* check cmp arg exps *)
      eret1 <- static_check_exp ctxt e1;
      eret2 <- static_check_exp ctxt e2;
      (* check for shape match *)
      if ~(sh_based_eq_shapes eret1.sh_based eret2.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "comparison given operands of different shapes in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return exp info *)
      return <| sh_based := WordB NotBased |>
    od ∧
  static_check_exp ctxt (Shift sh e n) =
    do
      (* check shifted exp *)
      eret <- static_check_exp ctxt e;
      (* check exp shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "shifted expression is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return exp info *)
      return (eret)
    od ∧
  static_check_exp ctxt BaseAddr =
    (* return exp info *)
    return <| sh_based := WordB Based |> ∧
  static_check_exp ctxt TopAddr =
    (* return exp info *)
    return <| sh_based := WordB Based |> ∧
  static_check_exp ctxt BytesInWordB =
    (* return exp info *)
    return <| sh_based := WordB NotBased |> ∧
  static_check_exps ctxt [] =
    (* return exps info *)
    return <| sh_baseds := [] |> ∧
  static_check_exps ctxt (e::es) =
    do
      (* check exps *)
      eret <- static_check_exp ctxt e;
      esret <- static_check_exps ctxt es;
      (* return exps info with combined basedness and all shapes *)
      return <| sh_baseds := eret.sh_based::esret.sh_baseds |>
    od
End


(*
  static_check_prog returns:
    (prog info (:prog_return)) static_result
*)
Definition static_check_prog_def:
  static_check_prog ctxt Skip =
    (* return prog info with no checks *)
    return <| exits_fun  := F
            ; exits_loop := F
            ; last       := OtherLast
            ; var_delta  := empty mlstring$compare
            ; curr_loc   := ctxt.loc |> ∧
  static_check_prog ctxt (Dec v s e p) =
    do
      (* check for redeclaration *)
      check_redec_var ctxt v;
      (* check initialising exp *)
      eret <- static_check_exp ctxt e;
      (* check for shape match *)
      if ~(sh_based_has_shape s eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "expression to initialise local variable "; v;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check prog with declared var *)
      ctxt' <<- ctxt with <| locals := insert ctxt.locals v <| vsh_based := eret.sh_based |>
                           ; last := OtherLast |>;
      pret <- static_check_prog ctxt' p;
      (* return prog info without declared var *)
      return <| exits_fun  := pret.exits_fun
              ; exits_loop := pret.exits_loop
              ; last       := pret.last
              ; var_delta  := delete pret.var_delta v
              ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (DecCall v s fname args p) =
    do
      (* check for redeclaration *)
      check_redec_var ctxt v;
      (* check func ptr exp and arg exps *)
      finf <- scope_check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(s = finf.ret_shape)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "call result to initialise local variable "; v;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt fname finf.params esret.sh_baseds;
      (* check prog with declared var *)
      ctxt' <<- ctxt with <| locals := insert ctxt.locals v <| vsh_based := sh_based_get Trusted s |>
                           ; last := OtherLast |>;
      pret <- static_check_prog ctxt' p;
      (* return prog info without declared var *)
      return <| exits_fun  := pret.exits_fun
              ; exits_loop := pret.exits_loop
              ; last       := pret.last
              ; var_delta  := delete pret.var_delta v
              ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (Assign Local v e) =
    do
      (* check for out of scope assignment *)
      vinf <- scope_check_local_var ctxt v;
      (* check assigning exp *)
      eret <- static_check_exp ctxt e;
      (* check for shape match *)
      if ~(sh_based_eq_shapes vinf.vsh_based eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "expression assigned to local variable "; v;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare v (vinf with <| vsh_based := eret.sh_based |>)
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Assign Global v e) =
    do
      (* check for out of scope assignment *)
      vinf <- scope_check_global_var ctxt v;
      (* check assigning exp *)
      eret <- static_check_exp ctxt e;
      (* check for shape match *)
      if ~(sh_based_has_shape vinf.vshape eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "expression assigned to global variable "; v;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
      static_check_prog ctxt (AssignCall (Local,rt) hdl trgt args) =
    do
      (* check for out of scope assignment *)
      vinf <- scope_check_local_var ctxt rt;
      (* check func ptr exp and arg exps *)
      finf <- scope_check_fun_name ctxt trgt;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(sh_based_has_shape finf.ret_shape vinf.vsh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "call result assigned to local variable "; rt;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt trgt finf.params esret.sh_baseds;
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
          do
            evinf <- scope_check_local_var ctxt evar;
            static_check_prog (ctxt with locals := insert ctxt.locals evar (evinf with <| vsh_based := sh_based_set Trusted evinf.vsh_based |>)) p;
            return ()
          od;
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare rt (vinf with <| vsh_based := sh_based_set Trusted vinf.vsh_based |>)
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (AssignCall (Global,rt) hdl trgt args) =
    do
      (* check for out of scope assignment *)
      vinf <- scope_check_global_var ctxt rt;
      (* check func ptr exp and arg exps *)
      finf <- scope_check_fun_name ctxt trgt;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(vinf.glob_shape = finf.ret_shape)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "call result assigned to global variable "; rt;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt trgt finf.params esret.sh_baseds;
      (* check exception handling info *)
      case hdl of
        NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
          do
            evinf <- scope_check_local_var ctxt evar;
            static_check_prog (ctxt with locals := insert ctxt.locals evar (evinf with <| based := Trusted |>)) p;
            return ()
          od;
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (AssignCall rt hdl trgt args) =
    do
      (* check for out of scope assignment *)
      vinf <- scope_check_local_var ctxt rt;
      (* check func ptr exp and arg exps *)
      finf <- scope_check_fun_name ctxt trgt;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(sh_based_has_shape finf.ret_shape vinf.vsh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "call result assigned to local variable "; rt;
           strlit " does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt trgt finf.params esret.sh_baseds;
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
          do
            evinf <- scope_check_local_var ctxt evar;
            static_check_prog (ctxt with locals := insert ctxt.locals evar (evinf with <| vsh_based := sh_based_set Trusted evinf.vsh_based |>)) p;
            return ()
          od;
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare rt (vinf with <| vsh_based := sh_based_set Trusted vinf.vsh_based |>)
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Return rt) =
    do
      (* check return value exp *)
      eret <- static_check_exp ctxt rt;
      (* lookup current function info *)
      finf <- case ctxt.scope of
              | FunScope fname => scope_check_fun_name ctxt fname
              (* should never occur if static checker implemented correctly *)
              | _ => error (GenErr $ strlit "return found outside function scope");
      (* check for shape match *)
      if ~(sh_based_has_shape finf.ret_shape eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "expression to return does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := T
              ; exits_loop := F
              ; last       := RetLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (TailCall trgt args) =
    do
      (* lookup current function info *)
      finf <- case ctxt.scope of
              | FunScope fname => scope_check_fun_name ctxt fname
              | _ => error (GenErr $ strlit "tail call found outside function scope");
      (* check func ptr exp and arg exps *)
      finf' <- scope_check_fun_name ctxt trgt;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(finf.ret_shape = finf'.ret_shape)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "call result to return does not match declared shape in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt trgt finf.params esret.sh_baseds;
      (* return prog info *)
      return <| exits_fun  := T
              ; exits_loop := F
              ; last       := TailLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (StandAloneCall hdl trgt args) =
    do
      (* check func ptr exp and arg exps *)
      finf <- scope_check_fun_name ctxt trgt;
      esret <- static_check_exps ctxt args;
      (* check arg num and shapes *)
      check_func_args ctxt trgt finf.params esret.sh_baseds;
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
          do
            evinf <- scope_check_local_var ctxt evar;
            static_check_prog (ctxt with locals := insert ctxt.locals evar (evinf with <| vsh_based := sh_based_set Trusted evinf.vsh_based |>)) p;
            return ()
          od;
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    do
      (* check arg exps *)
      esret <- static_check_exps ctxt [ptr1;len1;ptr2;len2];
      (* check arg shapes *)
      if ~(EVERY (sh_based_has_shape One) esret.sh_baseds)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "FFI call to "; fname;
           strlit " given a non-word operand in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Seq p1 p2) =
    do
      (* check for prior warnable unreachability *)
      (warn_p1, ctxt1) <<- reached_warnable p1 ctxt;
      case warn_p1 of
      | SOME ls => log (WarningErr $ get_unreach_msg ctxt1.loc (last_to_str ls) ctxt1.scope)
      | NONE   => return ();
      (* check first prog *)
      pret1 <- static_check_prog ctxt1 p1;
      (* update unreachability after first prog *)
      next_r <<- next_is_reachable ctxt1.is_reachable pret1.last;
      ctxt2 <<- ctxt1 with <|
          locals := seq_vbases ctxt1.locals pret1.var_delta
        ; is_reachable := next_r
        ; last := if next_now_unreachable ctxt1.is_reachable next_r
                    then pret1.last
                  else ctxt1.last
        ; loc := pret1.curr_loc
      |>;
      (* check for warnable unreachability after first prog *)
      (warn_p2, ctxt3) <<- reached_warnable p2 ctxt2;
      case warn_p2 of
      | SOME ls => log (WarningErr $ get_unreach_msg ctxt3.loc (last_to_str ls) ctxt1.scope)
      | NONE   => return ();
      (* check second prog *)
      pret2 <- static_check_prog ctxt3 p2;
      (* return prog info by combining both appropriately *)
      return <| exits_fun  := (pret1.exits_fun \/ pret2.exits_fun)
              ; exits_loop := (pret1.exits_loop \/ pret2.exits_loop)
              ; last       := seq_last_stmt pret1.last pret2.last
              ; var_delta  := seq_vbases pret1.var_delta pret2.var_delta
              ; curr_loc   := pret2.curr_loc |>
    od ∧
  static_check_prog ctxt (If e p1 p2) =
    do
      (* check condition exp *)
      eret <- static_check_exp ctxt e;
      (* check condition shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "if condition is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check branches *)
      pret1 <- static_check_prog ctxt p1;
      pret2 <- static_check_prog (ctxt with loc := pret1.curr_loc) p2;
      (* return prog info by combining both appropriately *)
      double_ret <<- (pret1.exits_fun /\ pret2.exits_fun);
      double_loop_exit <<- (pret1.exits_loop /\ pret2.exits_loop);
      return <|
        exits_fun  := double_ret
      ; exits_loop := double_loop_exit
      ; last       := branch_last_stmt double_ret double_loop_exit
      ; var_delta  := branch_vbases ctxt.locals pret1.var_delta pret2.var_delta
      ; curr_loc   := pret2.curr_loc |>
    od ∧
  static_check_prog ctxt (While e p) =
    do
      (* check condition exp *)
      eret <- static_check_exp ctxt e;
      (* check condition shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "while condition is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* check loop body *)
      pret <- static_check_prog (ctxt with in_loop := T) p;
      (* return prog info by treating like an else-less If *)
      return <|
        exits_fun  := F
      ; exits_loop := F
      ; last       := OtherLast
      ; var_delta  :=
          branch_vbases ctxt.locals pret.var_delta $ mlmap$empty mlstring$compare
      ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Break =
    do
      (* check for rogueness *)
      if ~ctxt.in_loop
        then error (GenErr $ get_rogue_msg T ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := T
              ; last       := BreakLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Continue =
    do
      (* check for rogueness *)
      if ~ctxt.in_loop
        then error (GenErr $ get_rogue_msg F ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := T
              ; last       := ContLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Raise eid excp) =
    do
      (* check exception value exp *)
      static_check_exp ctxt excp;
      (* return prog info *)
      return <| exits_fun  := T
              ; exits_loop := F
              ; last       := RaiseLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Store addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "store address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Store32 addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "store address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "store value is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (StoreByte addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "store address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB NotBased   => log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "store value is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemLoad mop Local v e) =
    do
      (* check for out of scope var *)
      vinf <- scope_check_local_var ctxt v;
      (* check address exp *)
      aret <- static_check_exp ctxt e;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "load address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB Based      => log (WarningErr $ get_memop_msg F T F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg F T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_based_has_shape One vinf.vsh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "load variable is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare v (vinf with <| vsh_based := sh_based_set Trusted vinf.vsh_based |>)
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemLoad mop Global v e) =
    do
      (* check for out of scope var *)
      vinf <- scope_check_global_var ctxt v;
      (* check address exp *)
      aret <- static_check_exp ctxt e;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "load address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB Based      => log (WarningErr $ get_memop_msg F T F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg F T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(One = vinf.vshape)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "load variable is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemStore mop a e) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt a;
      eret <- static_check_exp ctxt e;
      (* check address shape and references base *)
      case aret.sh_based of
      | StructB _        => error (ShapeErr $ concat
                            [ctxt.loc; strlit "store address is not a word in ";
                             get_scope_desc ctxt.scope; strlit "\n"])
      | WordB Based      => log (WarningErr $ get_memop_msg F F F ctxt.loc ctxt.scope)
      | WordB NotTrusted => log (WarningErr $ get_memop_msg F F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_based_has_shape One eret.sh_based)
        then error (ShapeErr $ concat
          [ctxt.loc; strlit "store value is not a word in ";
           get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Tick =
    (* return prog info with no checks *)
    return <| exits_fun  := F
              ; exits_loop := F
              ; last       := InvisLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |> ∧
  static_check_prog ctxt (Annot t str) =
    (* update current location *)
    let loc = if (t = «location»)
                then concat [strlit "AT "; str; strlit ": "]
              else ctxt.loc in
    (* return prog info with no checks *)
    return <| exits_fun  := F
            ; exits_loop := F
            ; last       := InvisLast
            ; var_delta  := empty mlstring$compare
            ; curr_loc   := loc |>
End

(*
  static_check_progs returns:
    (unit) static_result
*)
Definition static_check_progs_def:
  static_check_progs fctxt gctxt [] =
    (* no more decls *)
    return () ∧
  static_check_progs fctxt gctxt (Decl _ _ _::decls) =
    (* not a function *)
    static_check_progs fctxt gctxt decls ∧
  static_check_progs fctxt gctxt (Function fi::decls) =
    do
      (* setup initial checking context *)
      ctxt <<- <| locals := FOLDL (\m (v, s). insert m v <| vsh_based := sh_based_get Trusted s |>) (empty mlstring$compare) fi.params
                ; globals := gctxt
                ; funcs := fctxt
                ; scope := FunScope fi.name
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := strlit "" |>;
      (* check function body *)
      prog_ret <- static_check_prog ctxt fi.body;
      (* check missing function exit *)
      if ~(prog_ret.exits_fun)
        then error (GenErr $ concat
          [strlit "branches missing return statement in ";
           get_scope_desc (FunScope fi.name); strlit "\n"])
      else return ();
      (* check remaining functions *)
      static_check_progs fctxt gctxt decls
    od
End

(*
  static_check_decls returns:
    ((varname, global_info) map, (funname, func_info) map)
*)
Definition static_check_decls_def:
  static_check_decls fctxt gctxt [] =
    (* no more decls *)
    return (fctxt, gctxt) ∧
  static_check_decls fctxt gctxt (Decl shape vname exp::decls) =
    do
      (* setup initial checking context *)
      ctxt <<- <| locals := empty mlstring$compare
                ; globals := gctxt
                ; funcs := empty mlstring$compare
                ; scope := DeclScope vname
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := strlit "" |>;
      (* check for redeclaration *)
      check_redec_var (ctxt with scope := TopLevel) vname;
      (* check initialisation expression *)
      eret <- static_check_exp ctxt exp;
      (* check for shape match *)
      if ~(sh_based_has_shape shape eret.sh_based)
        then error (ShapeErr $ concat
          [strlit "expression to initialise global variable "; vname;
           strlit " does not match declared shape\n"])
      else return ();
      (* check remaining decls *)
      static_check_decls fctxt (insert gctxt vname <| vshape := shape |>) decls
    od ∧
  static_check_decls fctxt gctxt (Function fi::funs) =
    do
      (* check for redeclaration *)
      if member fi.fname fctxt
        then error (GenErr $ concat
        (* TODO: swap this to `get_redec_msg F <loc> f TopLevel` once function locations exist *)
          [strlit "function "; fi.name; strlit " is redeclared\n"])
      else return ();
      (* check main func *)
      if fi.name = «main»
        then do
          (* check main func args *)
          if LENGTH fi.params > 0
            then error (GenErr $ strlit "main function has arguments\n")
          else return ();
          (* check main func export status *)
          if fi.export
            then error (GenErr $ strlit "main function is exported\n")
          else return ();
          (* check main func return shape *)
          if ~(fi.return = One)
            then error (ShapeErr $ strlit "main function does not return a word\n")
          else return ();
        od
      else
        do
          (* check arg name uniqueness *)
          case first_repeat $ QSORT mlstring_lt (MAP FST fi.params) of
            SOME p => error (GenErr $ concat
              [strlit "parameter "; p; strlit " is redeclared in function ";
              fi.name; strlit "\n"])
          | NONE => return ();
          (* check exported func *)
          if fi.export
            then do
              (* check exported func arg num *)
              if LENGTH fi.params > 4
                then error (GenErr $ concat
                  [strlit "exported function "; fi.name;
                  strlit " has more than 4 arguments\n"])
              else return ();
              (* check exported func arg shape *)
              if EXISTS (\shape. ~(shape = One)) (MAP SND fi.params)
                then error (ShapeErr $ concat
                  [strlit "exported function "; fi.name;
                  strlit " has non-word argument/s\n"])
              else return ();
              (* check exported func return shape *)
              if ~(fi.return = One)
                then error (ShapeErr $ concat
                  [strlit "exported function "; fi.name;
                  strlit " does not return a word\n"])
              else return ();
            od
          else
            (* check func return shape size *)
            if size_of_shape fi.return > 32
              then error (ShapeErr $ concat
                [strlit "function "; fi.name;
                strlit " returns a shape bigger than 32 words\n"])
            else return () ;
        od ;
      (* check remaining decls *)
      static_check_decls
        (insert fctxt fi.name
          <| ret_shape := fi.return ; params := fi.params |>)
        gctxt decls
    od
End

(*
  static_check returns:
    (unit) static_result

  The static checker returns () if no error occurred, or the static error
  encountered, along with a list of warnings encountered (if any). All warnings
  and errors come with a message containing the issue and its location
*)
Definition static_check_def:
  static_check decls =
    do
      (* check decls and build context *)
      (fctxt, gctxt) <- static_check_decls (empty mlstring$compare) (empty mlstring$compare) decls;
      (* check function bodies with context *)
      static_check_progs fctxt gctxt decls
    od
End
