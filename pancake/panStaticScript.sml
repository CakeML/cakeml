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

Datatype:
  staterr = ScopeErr mlstring
          | WarningErr mlstring
          | GenErr mlstring
          | ShapeErr mlstring
End

(* (retval, proper error) error # warning list *)
Type static_result = ``:('a, staterr) error # staterr list``

Datatype:
  based = Based | NotBased | Trusted | NotTrusted
End

Datatype:
  reachable = IsReach | WarnReach | NotReach
End

Datatype:
  last_stmt =
    (* function exit *)
    RetLast | RaiseLast | TailLast
    (* loop exit *)
    | BreakLast | ContLast
    (* ambiguous exit (for conditional branches) *)
    | IfExitLast
    (* non-exit *)
    | InvisLast | OtherLast
End

Datatype:
  context = <| vars : (varname, based) map
             ; funcs : funname list
             ; fname : funname
             ; in_loop : bool
             ; is_reachable : reachable
             ; last : last_stmt
             ; loc : mlstring |>
End

(* functions for `based` *)

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

Definition based_cmp_def:
  based_cmp x y = if x = y then x else NotTrusted
End

Definition seq_vbases_def:
  seq_vbases x y = union y x
End

Definition branch_vbases_def:
  branch_vbases (vctxt: (varname, based) map) x y =
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

(* functions for `last_stmt` and `reachable` *)

Definition last_to_str_def:
  last_to_str l =
    case l of
    | RetLast    => implode "return"
    | RaiseLast  => implode "raise"
    | TailLast   => implode "tail call"
    | BreakLast  => implode "break"
    | ContLast   => implode "continue"
    | IfExitLast => implode "exiting conditional"
    | _          => implode ""
    (* only used to print exits in warnings *)
End

Definition last_is_exit_def:
  last_is_exit x = ~(x = InvisLast \/ x = OtherLast)
End

Definition next_is_reachable_def:
  next_is_reachable r x =
    case r of
    | IsReach => if last_is_exit x then WarnReach else IsReach
    | _ => r
End

Definition next_now_unreachable_def:
  next_now_unreachable r r' = (r = IsReach /\ ~(r' = IsReach))
End

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

Definition seq_last_stmt_def:
  seq_last_stmt x y = if y = InvisLast then x else y
End

Definition branch_last_stmt_def:
  branch_last_stmt double_ret = if double_ret then IfExitLast else OtherLast
End

(* misc functions *)

Definition first_repeat_def:
  first_repeat xs =
    case xs of
      (x1::x2::xs) =>
        if x1 = x2
          then SOME x1
        else first_repeat $ x2::xs
    | _ => NONE
End

Definition binop_to_str_def:
  binop_to_str op =
    case op of
    | Add => implode "Add"
    | Sub => implode "Sub"
    | And => implode "And"
    | Or  => implode "Or"
    | Xor => implode "Xor"
End

Definition panop_to_str_def:
  panop_to_str op =
    case op of
    | Mul => implode "Mul"
End


(*
  static_check_exp[s] returns:
    (basedness of expression (:based)) static_result
*)
Definition static_check_exp_def:
  static_check_exp ctxt (Const c) = return (NotBased) ∧
  static_check_exp ctxt (Var vname) =
    (case lookup ctxt.vars vname of
      NONE => error (ScopeErr $ concat
        [ctxt.loc;
         strlit "variable "; vname;  strlit " is not in scope in function ";
         ctxt.fname; strlit "\n"])
    | SOME x => return x) ∧
  static_check_exp ctxt (Label fname) =
    (if ¬MEM fname ctxt.funcs
      then error (ScopeErr $ concat
        [ctxt.loc;
         strlit "function "; fname; strlit " is not in scope in function ";
         ctxt.fname; strlit "\n"])
    else return (NotBased)) ∧
  static_check_exp ctxt (Struct es) =
    do
      static_check_exps ctxt es;
      return (Trusted)
      (* retval doesn't matter too much, since shape checking will pick up a struct being used an address*)
    od ∧
  static_check_exp ctxt (Field index e) =
    do
      static_check_exp ctxt e;
      return (NotTrusted)
    od ∧
  static_check_exp ctxt (Load shape e) =
    do
      b <- static_check_exp ctxt e;
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
      return (Trusted)
    od ∧
  static_check_exp ctxt (LoadByte e) =
    do
      b <- static_check_exp ctxt e;
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
      return (Trusted)
    od ∧
  static_check_exp ctxt (Op bop es) =
    do
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
      static_check_exps ctxt es
    od ∧
  static_check_exp ctxt (Panop pop es) =
    do
      nargs <<- LENGTH es;
      case pop of
      | Mul  => if ~(nargs = 2)
                  then error (GenErr $ concat
                    [ctxt.loc;
                     strlit "operation "; panop_to_str pop;
                     strlit " only accepts 2 operands, ";
                     num_to_str nargs; strlit " provided\n"])
                else return ();
      static_check_exps ctxt es
    od ∧
  static_check_exp ctxt (Cmp cmp e1 e2) =
    do
      static_check_exp ctxt e1;
      static_check_exp ctxt e2;
      return (NotBased)
    od ∧
  static_check_exp ctxt (Shift sh e n) = static_check_exp ctxt e ∧
  static_check_exp ctxt BaseAddr = return (Based) ∧
  static_check_exp ctxt BytesInWord = return (NotBased) ∧
  static_check_exps ctxt [] = return (NotBased) ∧
  static_check_exps ctxt (e::es) =
    do
      b1 <- static_check_exp ctxt e;
      b2 <- static_check_exps ctxt es;
      return (based_merge b1 b2)
      (* retval only applies to operations - use of check_exps for eg. args ignores the return *)
    od
End

(*
  static_check_prog returns:
    (
      whether prog returns in all execution paths (:bool),
      reachability of context BEFORE prog (:reachable),
      last statement of prog wrt reachability (:last_stmt),
      change in variable mapping as a result of prog (:(variable,based) map),
      last found location string (:mlstring)
    ) static_result
*)
Definition static_check_prog_def:
  static_check_prog ctxt Skip =
    return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc) ∧
  static_check_prog ctxt (Dec v e p) =
    do
      case lookup ctxt.vars v of
        SOME _ => log (WarningErr $ concat
          [ctxt.loc;
           strlit "variable "; v; strlit " is redeclared in function ";
           ctxt.fname; strlit "\n"])
      | NONE => return ();
      b <- static_check_exp ctxt e;
      ctxt' <<- ctxt with <| vars := insert ctxt.vars v b
                           ; last := OtherLast |>;
      (rt, rh, ls, vs, loc) <- static_check_prog ctxt' p;
      return (rt, ctxt.is_reachable, ls, delete vs v, loc)
    od ∧
  static_check_prog ctxt (DecCall v s e args p) =
    do
      case lookup ctxt.vars v of
        SOME _ => log (WarningErr $ concat
          [ctxt.loc;
          strlit "variable "; v; strlit " is redeclared in function ";
          ctxt.fname; strlit "\n"])
      | NONE => return ();
      static_check_exp ctxt e;
      static_check_exps ctxt args;
      ctxt' <<- ctxt with <| vars := insert ctxt.vars v Trusted
                           ; last := OtherLast |>;
      (rt, rh, ls, vs, loc) <- static_check_prog ctxt' p;
      return (rt, ctxt.is_reachable, ls, delete vs v, loc)
    od ∧
  static_check_prog ctxt (Assign v e) =
    do
      case lookup ctxt.vars v of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
          strlit "variable "; v; strlit " is not in scope in function ";
          ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      b <- static_check_exp ctxt e;
      return (F, ctxt.is_reachable, OtherLast, singleton mlstring$compare v b, ctxt.loc)
    od ∧
  static_check_prog ctxt (Store dest src) =
    do
      b <- static_check_exp ctxt dest;
      static_check_exp ctxt src;
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
      return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (StoreByte dest src) =
    do
      b <- static_check_exp ctxt dest;
      static_check_exp ctxt src;
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
      return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (Seq p1 p2) =
    do
      (warn_p1, ctxt1) <<- reached_warnable p1 ctxt;
      case warn_p1 of
      | SOME ls => log (WarningErr $ concat
          [ctxt1.loc;
           strlit "unreachable statement(s) after "; last_to_str ls;
           strlit " in function " ; ctxt1.fname; strlit "\n"])
      | NONE   => return ();
      (rt1, rh1, ls1, vs1, loc1) <- static_check_prog ctxt1 p1;
      next_r <<- next_is_reachable rh1 ls1;
      ctxt2 <<- ctxt1 with <| vars := seq_vbases ctxt1.vars vs1
                             ; is_reachable := next_r
                             ; last := if next_now_unreachable ctxt1.is_reachable next_r then ls1 else ctxt1.last
                             ; loc := loc1 |>;
      (warn_p2, ctxt3) <<- reached_warnable p2 ctxt2;
      case warn_p2 of
      | SOME ls => log (WarningErr $ concat
          [ctxt3.loc;
           strlit "unreachable statement(s) after "; last_to_str ls;
           strlit " in function " ; ctxt1.fname; strlit "\n"])
      | NONE   => return ();
      (rt2, rh2, ls2, vs2, loc2) <- static_check_prog ctxt3 p2;
      return ((rt1 \/ rt2), ctxt3.is_reachable, seq_last_stmt ls1 ls2, seq_vbases vs1 vs2, loc2)
    od ∧
  static_check_prog ctxt (If e p1 p2) =
    do
      static_check_exp ctxt e;
      (rt1, rh1, ls1, vs1, loc1) <- static_check_prog ctxt p1;
      (rt2, rh2, ls2, vs2, loc2) <- static_check_prog (ctxt with loc := loc1) p2;
      double_ret <<- (rt1 /\ rt2);
      return (double_ret, ctxt.is_reachable, branch_last_stmt double_ret, branch_vbases ctxt.vars vs1 vs2, loc2)
    od ∧
  static_check_prog ctxt (While e p) =
    do
      static_check_exp ctxt e;
      (rt, rh, ls, vs, loc) <- static_check_prog (ctxt with in_loop := T) p;
      (* While is statically similar to else-less If: *)
      return (F, ctxt.is_reachable, OtherLast, branch_vbases ctxt.vars vs $ mlmap$empty mlstring$compare, loc)
    od ∧
  static_check_prog ctxt Break =
    do
      if ~ctxt.in_loop
        then error (GenErr $ concat
          [ctxt.loc;
           strlit "break statement outside loop in function ";
           ctxt.fname; strlit "\n"])
      else return ();
      return (F, ctxt.is_reachable, BreakLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt Continue =
    do
      if ~ctxt.in_loop
        then error (GenErr $ concat
          [ctxt.loc;
           strlit "continue statement outside loop in function ";
           ctxt.fname; strlit "\n"])
      else return ();
      return (F, ctxt.is_reachable, ContLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (TailCall trgt args) =
    do
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      return (T, ctxt.is_reachable, TailLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (AssignCall rt hdl trgt args) =
    do
      case lookup ctxt.vars rt of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
           strlit "variable "; rt; strlit " is not in scope in function ";
           ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      case hdl of
        NONE => return ()
      | SOME (eid, evar, p) =>
        case lookup ctxt.vars evar of
          NONE => error (ScopeErr $ concat
            [ctxt.loc;
             strlit "variable "; evar; strlit " is not in scope in function ";
             ctxt.fname; strlit "\n"])
        | SOME _ =>
            do
              static_check_prog (ctxt with vars := insert ctxt.vars evar Trusted) p;
              return ()
            od;
      return (F, ctxt.is_reachable, OtherLast, singleton mlstring$compare rt Trusted, ctxt.loc)
    od ∧
  static_check_prog ctxt (StandAloneCall hdl trgt args) =
    do
      static_check_exp ctxt trgt;
      static_check_exps ctxt args;
      case hdl of
        NONE => return ()
      | SOME (eid, evar, p) =>
        case lookup ctxt.vars evar of
          NONE => error (ScopeErr $ concat
            [ctxt.loc;
             strlit "variable "; evar; strlit " is not in scope in function ";
             ctxt.fname; strlit "\n"])
        | SOME _ =>
            do
              static_check_prog (ctxt with vars := insert ctxt.vars evar Trusted) p;
              return ()
            od;
      return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    do
      static_check_exps ctxt [ptr1;len1;ptr2;len2];
      return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (Raise eid excp) =
    do
      static_check_exp ctxt excp;
      return (T, ctxt.is_reachable, RaiseLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (Return rt) =
    do
      static_check_exp ctxt rt;
      return (T, ctxt.is_reachable, RetLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt (ShMemLoad mop v e) =
    do
      case lookup ctxt.vars v of
        NONE => error (ScopeErr $ concat
          [ctxt.loc;
           strlit "variable "; v; strlit " is not in scope in function ";
           ctxt.fname; strlit "\n"])
      | SOME _ => return ();
      b <- static_check_exp ctxt e;
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
      return (F, ctxt.is_reachable, OtherLast, singleton mlstring$compare v Trusted, ctxt.loc)
    od ∧
  static_check_prog ctxt (ShMemStore mop e1 e2) =
    do
      b <- static_check_exp ctxt e1;
      static_check_exp ctxt e2;
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
      return (F, ctxt.is_reachable, OtherLast, empty mlstring$compare, ctxt.loc)
    od ∧
  static_check_prog ctxt Tick = return (F, ctxt.is_reachable, InvisLast, empty mlstring$compare, ctxt.loc) ∧
  static_check_prog ctxt (Annot t str) =
    let loc = if (t = «location»)
                then concat [strlit "AT "; str; strlit ": "]
              else ctxt.loc in
    return (F, ctxt.is_reachable, InvisLast, empty mlstring$compare, loc)
End

(*
  static_check_funs returns:
    (unit) static_result
*)
Definition static_check_funs_def:
  static_check_funs fnames [] = return () ∧
  static_check_funs fnames ((fname, export:bool, vshapes, body)::funs) =
    do
      if (fname = «main» /\ LENGTH vshapes > 0) then
        error (GenErr $ strlit "main function has arguments\n")
      else return ();
      if (fname = «main» /\ export) then
        error (GenErr $ strlit "main function is exported\n")
      else return ();
      if (LENGTH vshapes > 4 /\ export) then
        error (GenErr $ concat
          [strlit "exported function "; fname;
           strlit " has more than 4 arguments\n"])
      else return ();
      pnames <<- MAP FST vshapes;
      case first_repeat $ QSORT mlstring_lt pnames of
        SOME p => error (GenErr $ concat
          [strlit "parameter "; p; strlit " is redeclared in function ";
           fname; strlit "\n"])
      | NONE => return ();
      ctxt <<- <| vars := FOLDL (\m p. insert m p Trusted) (empty mlstring$compare) pnames
                ; funcs := fnames
                ; fname := fname
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := strlit "" |>;
      (returned, _, _, _, _) <- static_check_prog ctxt body;
      if ~returned
        then error (GenErr $ concat
          [strlit "branches missing return statement in function ";
           fname; strlit "\n"])
      else return ();
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
      fnames <<- MAP FST funs;
      case first_repeat $ QSORT mlstring_lt fnames of
        SOME f => error (GenErr $ concat
          [strlit "function "; f; strlit " is redeclared\n"])
      | NONE => return ();
      static_check_funs fnames funs
    od
End

val _ = export_theory ();
