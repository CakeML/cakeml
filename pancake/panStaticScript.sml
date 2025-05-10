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


open preamble errorLogMonadTheory panLangTheory mlmapTheory mlintTheory;

val _ = new_theory "panStatic";


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

(* Type for holding var state *)
Type var_info = ``:(varname, based) map``

(* Record for current (per-func) context *)
Datatype:
  context = <|
    vars         : var_info     (* tracked var state *)
  ; funcs        : funname list (* all function info *)
  ; fname        : funname      (* current function info *)
  ; in_loop      : bool         (* loop status *)
  ; is_reachable : reachable    (* reachability *)
  ; last         : last_stmt    (* exit-ness of last statement *)
  ; loc          : mlstring     (* location string *)
  |>
End

(* Record for static_check_prog returns *)
Datatype:
  prog_return = <|
    exits_fun  : bool       (* func exit status for all paths *)
  ; exits_loop : bool       (* loop exit status for all paths *)
  ; last       : last_stmt  (* new exit-ness of last statement *)
  ; var_delta  : var_info   (* change in var state *)
  ; curr_loc   : mlstring   (* latest location string *)
  |>
End


(* Functions for `based` *)

(* Determine based-ness according to priority *)
Definition based_merge_def:
  based_merge x y =
    case (x,y) of
      (Based, _) => Based
    | (_, Based) => Based
    | (NotTrusted, _) => NotTrusted
    | (_, NotTrusted) => NotTrusted
    | (Trusted, _) => Trusted
    | (_, Trusted) => Trusted
    | (NotBased, NotBased) => NotBased
End

(* Comparison for combining based-ness between If/While branches *)
Definition based_cmp_def:
  based_cmp x y = if x = y then x else NotTrusted
End

(*
  Combine var state deltas of If/While branches
    where states are either combined between the two deltas (if in both) or with
    prior context (if in just one)
  Needs extension with extension of `var_info` type
*)
Definition branch_vbases_def:
  branch_vbases (vctxt: var_info) x y =
    let x' = mapWithKey (\k v.
              if ~(member k y) then
                case lookup vctxt k of
                  SOME v' => based_cmp v v'
                | NONE => NotTrusted
              else v) x;
        y' = mapWithKey (\k v.
              if ~(member k x) then
                case lookup vctxt k of
                  SOME v' => based_cmp v v'
                | NONE => NotTrusted
              else v) y
    in unionWith based_cmp x' y'
End

(* Combine var state deltas of Seq progs *)
Definition seq_vbases_def:
  seq_vbases x y = union y x
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


(* Misc functions *)

(* Find the first element in a sorted list that is repeated *)
Definition first_repeat_def:
  first_repeat xs =
    case xs of
      (x1::x2::xs) =>
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


(* Static checking functions *)

(*
  static_check_exp[s] returns:
    (basedness of expression (:based)) static_result
*)
Definition static_check_exp_def:
  static_check_exp ctxt (Const c) =
    (* return based-ness *)
    return (NotBased) ∧
  static_check_exp ctxt (Var vname) =
    (* check for out of scope var *)
    (case lookup ctxt.vars vname of
      NONE => error (ScopeErr $ concat
        [ctxt.loc;
         strlit "variable "; vname;  strlit " is not in scope in function ";
         ctxt.fname; strlit "\n"])
      (* return stored based-ness *)
    | SOME x => return x) ∧
  static_check_exp ctxt (Label fname) =
    (* check for out of scope func *)
    (if ¬MEM fname ctxt.funcs
      then error (ScopeErr $ concat
        [ctxt.loc;
         strlit "function "; fname; strlit " is not in scope in function ";
         ctxt.fname; strlit "\n"])
    (* return based-ness *)
    else return (NotBased)) ∧
  static_check_exp ctxt (Struct es) =
    do
      (* check struct field exps *)
      static_check_exps ctxt es;
      (* return based-ness *)
      return (Trusted)
      (* retval doesn't matter too much, since future shape checking will pick
        up a struct being used an address *)
    od ∧
  static_check_exp ctxt (Field index e) =
    do
      (* check struct exp *)
      static_check_exp ctxt e;
      (* return based-ness *)
      return (NotTrusted)
    od ∧
  static_check_exp ctxt (Load shape addr) =
    do
      (* check addr exp *)
      b <- static_check_exp ctxt addr;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | _          => return ();
      (* return based-ness *)
      return (Trusted)
    od ∧
  static_check_exp ctxt (Load32 addr) =
    do
      (* check addr exp *)
      b <- static_check_exp ctxt addr;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | Based      => return ()
      | Trusted    => return ();
      (* return based-ness *)
      return (Trusted)
    od ∧
  static_check_exp ctxt (LoadByte addr) =
    do
      (* check addr exp *)
      b <- static_check_exp ctxt addr;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local load address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | Based      => return ()
      | Trusted    => return ();
      (* return based-ness *)
      return (Trusted)
    od ∧
  static_check_exp ctxt (Op bop es) =
    do
      (* check num of op args *)
      nargs <<- LENGTH es;
      case bop of
      | Sub  => if ~(nargs = 2)
                  then error (GenErr $ concat
                    [ctxt.loc;
                     strlit "operation "; binop_to_str bop;
                     strlit " only accepts 2 operands, ";
                     num_to_str nargs; strlit " provided\n"])
                else return ()
      | _    => if nargs < 2
                  then error (GenErr $ concat
                    [ctxt.loc;
                     strlit "operation "; binop_to_str bop;
                     strlit " requires at least 2 operands, ";
                     num_to_str nargs; strlit " provided\n"])
                else return ();
      (* return combined based-ness of checked op args *)
      static_check_exps ctxt es
    od ∧
  static_check_exp ctxt (Panop pop es) =
    do
      (* check num of op args *)
      nargs <<- LENGTH es;
      case pop of
      | Mul  => if ~(nargs = 2)
                  then error (GenErr $ concat
                    [ctxt.loc;
                     strlit "operation "; panop_to_str pop;
                     strlit " only accepts 2 operands, ";
                     num_to_str nargs; strlit " provided\n"])
                else return ();
      (* return combined based-ness of checked op args *)
      static_check_exps ctxt es
    od ∧
  static_check_exp ctxt (Cmp cmp e1 e2) =
    do
      (* check cmp arg exps *)
      static_check_exp ctxt e1;
      static_check_exp ctxt e2;
      (* return based-ness *)
      return (NotBased)
    od ∧
  static_check_exp ctxt (Shift sh e n) =
    (* return based-ness of checked shifted exp *)
    static_check_exp ctxt e ∧
  static_check_exp ctxt BaseAddr =
    (* return based-ness *)
    return (Based) ∧
  static_check_exp ctxt BytesInWord =
    (* return based-ness *)
    return (NotBased) ∧
  static_check_exps ctxt [] =
    (* return based-ness *)
    return (NotBased) ∧
  static_check_exps ctxt (e::es) =
    do
      (* check exps *)
      b1 <- static_check_exp ctxt e;
      b2 <- static_check_exps ctxt es;
      (* return combined based-ness *)
      return (based_merge b1 b2)
      (* retval only applies to operations; use of check_exps for eg. args
          ignores the return *)
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
  static_check_prog ctxt (Dec v e p) =
    do
      (* check for reclaration *)
      case lookup ctxt.vars v of
        SOME _ => log (WarningErr $ concat
          [ctxt.loc;
           strlit "variable "; v; strlit " is redeclared in function ";
           ctxt.fname; strlit "\n"])
      | NONE => return ();
      (* check initialising exp *)
      b <- static_check_exp ctxt e;
      (* check prog with declared var *)
      ctxt' <<- ctxt with <| vars := insert ctxt.vars v b
                           ; last := OtherLast |>;
      pret <- static_check_prog ctxt' p;
      (* return prog info without declared var *)
      return <| exits_fun  := pret.exits_fun
              ; exits_loop := pret.exits_loop
              ; last       := pret.last
              ; var_delta  := delete pret.var_delta v
              ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (DecCall v s e args p) =
    do
      (* check for redeclaration *)
      case lookup ctxt.vars v of
        SOME _ => log (WarningErr $ concat
          [ctxt.loc;
          strlit "variable "; v; strlit " is redeclared in function ";
          ctxt.fname; strlit "\n"])
      | NONE => return ();
      (* check func ptr exp and arg exps *)
      static_check_exp ctxt e;
      static_check_exps ctxt args;
      (* check prog with declared var *)
      ctxt' <<- ctxt with <| vars := insert ctxt.vars v Trusted
                           ; last := OtherLast |>;
      pret <- static_check_prog ctxt' p;
      (* return prog info without declared var *)
      return <| exits_fun  := pret.exits_fun
              ; exits_loop := pret.exits_loop
              ; last       := pret.last
              ; var_delta  := delete pret.var_delta v
              ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (Assign v e) =
    do
      (* check for out of scope assignment *)
      case lookup ctxt.vars v of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
          strlit "variable "; v; strlit " is not in scope in function ";
          ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      (* check assigning exp *)
      b <- static_check_exp ctxt e;
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare v b
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Store addr exp) =
    do
      (* check address and value exps *)
      b <- static_check_exp ctxt addr;
      static_check_exp ctxt exp;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | Based      => return ()
      | Trusted    => return ();
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
      b <- static_check_exp ctxt addr;
      static_check_exp ctxt exp;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | _          => return ();
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
      b <- static_check_exp ctxt addr;
      static_check_exp ctxt exp;
      (* check address references base *)
      case b of
      | NotBased   => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address is not calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "local store address may not be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | _          => return ();
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
      | SOME ls => log (WarningErr $ concat
          [ctxt1.loc;
           strlit "unreachable statement(s) after "; last_to_str ls;
           strlit " in function " ; ctxt1.fname; strlit "\n"])
      | NONE   => return ();
      (* check first prog *)
      pret1 <- static_check_prog ctxt1 p1;
      (* update unreachability after first prog *)
      next_r <<- next_is_reachable ctxt1.is_reachable pret1.last;
      ctxt2 <<- ctxt1 with <|
          vars := seq_vbases ctxt1.vars pret1.var_delta
        ; is_reachable := next_r
        ; last := if next_now_unreachable ctxt1.is_reachable next_r
                    then pret1.last
                  else ctxt1.last
        ; loc := pret1.curr_loc
      |>;
      (* check for warnable unreachability after first prog *)
      (warn_p2, ctxt3) <<- reached_warnable p2 ctxt2;
      case warn_p2 of
      | SOME ls => log (WarningErr $ concat
          [ctxt3.loc;
           strlit "unreachable statement(s) after "; last_to_str ls;
           strlit " in function " ; ctxt1.fname; strlit "\n"])
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
      static_check_exp ctxt e;
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
      ; var_delta  := branch_vbases ctxt.vars pret1.var_delta pret2.var_delta
      ; curr_loc   := pret2.curr_loc |>
    od ∧
  static_check_prog ctxt (While e p) =
    do
      (* check condition exp *)
      static_check_exp ctxt e;
      (* check loop body *)
      pret <- static_check_prog (ctxt with in_loop := T) p;
      (* return prog info by treating like an else-less If *)
      return <|
        exits_fun  := F
      ; exits_loop := F
      ; last       := OtherLast
      ; var_delta  :=
          branch_vbases ctxt.vars pret.var_delta $ mlmap$empty mlstring$compare
      ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Break =
    do
      (* check for rogueness *)
      if ~ctxt.in_loop
        then error (GenErr $ concat
          [ctxt.loc;
           strlit "break statement outside loop in function ";
           ctxt.fname; strlit "\n"])
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
        then error (GenErr $ concat
          [ctxt.loc;
           strlit "continue statement outside loop in function ";
           ctxt.fname; strlit "\n"])
      else return ();
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := T
              ; last       := ContLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (TailCall trgt args) =
    do
      (* check func ptr exp and arg exps *)
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      (* return prog info *)
      return <| exits_fun  := T
              ; exits_loop := F
              ; last       := TailLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (AssignCall rt hdl trgt args) =
    do
      (* check for out of scope assignment *)
      case lookup ctxt.vars rt of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
           strlit "variable "; rt; strlit " is not in scope in function ";
           ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      (* check func ptr exp and arg exps *)
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      (* check exception handling info *)
      case hdl of
        NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
        case lookup ctxt.vars evar of
          NONE => error (ScopeErr $ concat
            [ctxt.loc;
             strlit "variable "; evar; strlit " is not in scope in function ";
             ctxt.fname; strlit "\n"])
          (* check handler prog *)
        | SOME _ =>
            do
              static_check_prog (ctxt with vars := insert ctxt.vars evar Trusted) p;
              return ()
            od;
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare rt Trusted
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (StandAloneCall hdl trgt args) =
    do
      (* check func ptr exp and arg exps *)
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      (* check exception handling info *)
      case hdl of
        NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, p) =>
        case lookup ctxt.vars evar of
          NONE => error (ScopeErr $ concat
            [ctxt.loc;
             strlit "variable "; evar; strlit " is not in scope in function ";
             ctxt.fname; strlit "\n"])
          (* check handler prog *)
        | SOME _ =>
            do
              static_check_prog (ctxt with vars := insert ctxt.vars evar Trusted) p;
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
      static_check_exps ctxt [ptr1;len1;ptr2;len2];
      (* return prog info *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
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
  static_check_prog ctxt (Return rt) =
    do
      (* check return value exp *)
      static_check_exp ctxt rt;
      (* return prog info *)
      return <| exits_fun  := T
              ; exits_loop := F
              ; last       := RetLast
              ; var_delta  := empty mlstring$compare
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemLoad mop v e) =
    do
      (* check for out of scope var *)
      case lookup ctxt.vars v of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
           strlit "variable "; v; strlit " is not in scope in function ";
           ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      (* check address exp *)
      b <- static_check_exp ctxt e;
      (* check address does not reference base *)
      case b of
      | Based      => log (WarningErr $ concat
          [ctxt.loc;
           strlit "shared load address is calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "shared load address may be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | _          => return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare v Trusted
              ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemStore mop a e) =
    do
      (* check address and value exps *)
      b <- static_check_exp ctxt a;
      static_check_exp ctxt e;
      (* check address does not reference base *)
      case b of
      | Based      => log (WarningErr $ concat
          [ctxt.loc;
           strlit "shared store address is calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | NotTrusted => log (WarningErr $ concat
          [ctxt.loc;
           strlit "shared store address may be calculated from base in function ";
           ctxt.fname; strlit "\n"])
      | _          => return ();
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
  static_check_funs returns:
    (unit) static_result
*)
Definition static_check_funs_def:
  static_check_funs fnames [] =
    (* no more functions *)
    return () ∧
  static_check_funs fnames ((fname, export:bool, vshapes, body)::funs) =
    do
      (* check main function arguments *)
      if (fname = «main» /\ LENGTH vshapes > 0) then
        error (GenErr $ strlit "main function has arguments\n")
      else return ();
      (* check main function export status *)
      if (fname = «main» /\ export) then
        error (GenErr $ strlit "main function is exported\n")
      else return ();
      (* check exported function arg num *)
      if (LENGTH vshapes > 4 /\ export) then
        error (GenErr $ concat
          [strlit "exported function "; fname;
           strlit " has more than 4 arguments\n"])
      else return ();
      (* check parameter name uniqueness *)
      pnames <<- MAP FST vshapes;
      case first_repeat $ QSORT mlstring_lt pnames of
        SOME p => error (GenErr $ concat
          [strlit "parameter "; p; strlit " is redeclared in function ";
           fname; strlit "\n"])
      | NONE => return ();
      (* setup initial checking context *)
      ctxt <<- <| vars := FOLDL (\m p. insert m p Trusted) (empty mlstring$compare) pnames
                ; funcs := fnames
                ; fname := fname
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := strlit "" |>;
      (* check function body *)
      prog_ret <- static_check_prog ctxt body;
      (* check missing function exit *)
      if ~(prog_ret.exits_fun)
        then error (GenErr $ concat
          [strlit "branches missing return statement in function ";
           fname; strlit "\n"])
      else return ();
      (* check remaining functions *)
      static_check_funs fnames funs
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
  static_check funs =
    do
      (* check func name uniqueness *)
      fnames <<- MAP FST funs;
      case first_repeat $ QSORT mlstring_lt fnames of
        SOME f => error (GenErr $ concat
          [strlit "function "; f; strlit " is redeclared\n"])
      | NONE => return ();
      (* check functions *)
      static_check_funs fnames funs
    od
End

val _ = export_theory ();
