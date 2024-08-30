(*
  Scope checking for Pancake.
*)

open preamble errorLogMonadTheory panLangTheory;

val _ = new_theory "panScope";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "errorLog";

Datatype:
  context = <| vars : varname list
             ; funcs : funname list
             ; fname : funname
             ; in_loop : bool |>
End

Datatype:
  staterr = ScopeErr mlstring
          | WarningErr mlstring
          | GenErr mlstring
          | ShapeErr mlstring
End

Type static_result = ``:('a, staterr) error # staterr list``

Definition first_repeat_def:
  first_repeat xs =
    case xs of
      (x1::x2::xs) =>
        if x1 = x2
          then SOME x1
        else first_repeat $ x2::xs
    | _ => NONE
End

(* Definition mapM_def:
  mapM f [] = return [] ∧
  mapM f (x::xs) = do
    e <- f x;
    es <- mapM f xs;
    return (e::es);
  od
End *)

Definition scope_check_exp_def:
  scope_check_exp ctxt (Const c) = return () ∧
  scope_check_exp ctxt (Var vname) =
    (if ¬MEM vname ctxt.vars
      then error (ScopeErr $ concat [strlit "variable "; vname; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
    else return ()) ∧
  scope_check_exp ctxt (Label fname) =
    (if ¬MEM fname ctxt.funcs
      then error (ScopeErr $ concat [strlit "function "; fname; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
    else return ()) ∧
  scope_check_exp ctxt (Struct es) =
    scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Field index e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Load shape e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (LoadByte e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Op bop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Panop pop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Cmp cmp e1 e2) =
    do
      scope_check_exp ctxt e1;
      scope_check_exp ctxt e2
    od ∧
  scope_check_exp ctxt (Shift sh e n) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt BaseAddr = return () ∧
  scope_check_exp ctxt BytesInWord = return () ∧
  scope_check_exps ctxt [] = return () ∧
  scope_check_exps ctxt (e::es) =
    do
      scope_check_exp ctxt e;
      scope_check_exps ctxt es
    od
End

Definition scope_check_prog_def:
  scope_check_prog ctxt Skip = return F ∧
  scope_check_prog ctxt (Dec v e p) =
    do
      if MEM v ctxt.vars
        then log (WarningErr $ concat [strlit "variable "; v; strlit " is redeclared in function "; ctxt.fname; strlit "\n"])
      else return ();
      scope_check_exp ctxt e;
      scope_check_prog (ctxt with vars := v :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (DecCall v s e args p) =
    do
      if MEM v ctxt.vars
        then log (WarningErr $ concat [strlit "variable "; v; strlit " is redeclared in function "; ctxt.fname; strlit "\n"])
      else return ();
      scope_check_exp ctxt e;
      scope_check_exps ctxt args;
      scope_check_prog (ctxt with vars := v :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (Assign v e) =
    do
      if ¬MEM v ctxt.vars
          then error (ScopeErr $ concat [strlit "variable "; v; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
      else scope_check_exp ctxt e;
      return F
    od ∧
  scope_check_prog ctxt (Store ad v) =
    do
      scope_check_exp ctxt ad;
      scope_check_exp ctxt v;
      return F
    od ∧
  scope_check_prog ctxt (StoreByte dest src) =
    do
      scope_check_exp ctxt dest;
      scope_check_exp ctxt src;
      return F
    od ∧
  scope_check_prog ctxt (Seq p1 p2) =
    do
      case p1 of
        (Seq _ (Return _))     => log (WarningErr $ concat [strlit "statements after return in function ";    ctxt.fname; strlit "\n"])
      | (Seq _ (Raise _ _))    => log (WarningErr $ concat [strlit "statements after raise in function ";     ctxt.fname; strlit "\n"])
      | (Seq _ (TailCall _ _)) => log (WarningErr $ concat [strlit "statements after tail call in function "; ctxt.fname; strlit "\n"])
      | _ => return ();
      rt1 <- scope_check_prog ctxt p1;
      rt2 <- scope_check_prog ctxt p2;
      return (rt1 \/ rt2)
    od ∧
  scope_check_prog ctxt (If e p1 p2) =
    do
      scope_check_exp ctxt e;
      rt1 <- scope_check_prog ctxt p1;
      rt2 <- scope_check_prog ctxt p2;
      return (rt1 /\ rt2)
    od ∧
  scope_check_prog ctxt (While e p) =
    do
      scope_check_exp ctxt e;
      scope_check_prog (ctxt with in_loop := T) p
    od ∧
  scope_check_prog ctxt Break =
    do
      if ~ctxt.in_loop
        then error (GenErr $ concat [strlit "break statement outside loop in function "; ctxt.fname; strlit "\n"])
      else return ();
      return F
    od ∧
  scope_check_prog ctxt Continue =
    do
      if ~ctxt.in_loop
        then error (GenErr $ concat [strlit "continue statement outside loop in function "; ctxt.fname; strlit "\n"])
      else return ();
      return F
    od ∧
  scope_check_prog ctxt (TailCall trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args;
      return T
    od ∧
  scope_check_prog ctxt (AssignCall rt hdl trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args;
      if ¬MEM rt ctxt.vars
        then error (ScopeErr $ concat [strlit "variable "; rt; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
      else
        case hdl of
          NONE => return F
        | SOME (eid, evar, p) =>
            if ¬MEM evar ctxt.vars
              then error (ScopeErr $ concat [strlit "variable "; evar; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
            else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p;
      return F
    od ∧
  scope_check_prog ctxt (StandAloneCall hdl trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args;
      case hdl of
        NONE => return F
      | SOME (eid, evar, p) =>
          if ¬MEM evar ctxt.vars
            then error (ScopeErr $ concat [strlit "variable "; evar; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
          else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p;
      return F
    od ∧
  scope_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    do
      scope_check_exps ctxt [ptr1;len1;ptr2;len2];
      return F
    od ∧
  scope_check_prog ctxt (Raise eid excp) =
    do
      scope_check_exp ctxt excp;
      return T
    od ∧
  scope_check_prog ctxt (Return rt) =
    do
      scope_check_exp ctxt rt;
      return T
    od ∧
  scope_check_prog ctxt (ShMemLoad mop v e) =
    do
      if ¬MEM v ctxt.vars
        then error (ScopeErr $ concat [strlit "variable "; v; strlit " is not in scope in function "; ctxt.fname; strlit "\n"])
      else scope_check_exp ctxt e;
      return F
    od ∧
  scope_check_prog ctxt (ShMemStore mop e1 e2) =
    do
      scope_check_exp ctxt e1;
      scope_check_exp ctxt e2;
      return F
    od ∧
  scope_check_prog ctxt Tick = return F ∧
  scope_check_prog ctxt (Annot _ _) = return F
End

Definition scope_check_funs_def:
  scope_check_funs fnames [] = return () ∧
  scope_check_funs fnames ((fname, _:bool, vshapes, body)::funs) =
    do
      ctxt <<- <| vars := MAP FST vshapes ; funcs := fnames ; fname := fname ; in_loop := F |>;
      returned <- scope_check_prog ctxt body;
      if ~returned
        then error (GenErr $ concat [strlit "branches missing return statement in function "; fname; strlit "\n"])
      else return ();
      scope_check_funs fnames funs
    od
End

(* The scope checker returns NONE to indicate that there is no scope error, and
   SOME (name, fname) to indicate that name is not in scope in an expression
   within the function fname. The first component name may be the name of a
   variable or a function. *)
Definition scope_check_def:
  scope_check funs =
    do
      fnames <<- MAP FST funs;
      case first_repeat $ QSORT mlstring_lt fnames of
        SOME f => error (GenErr $ concat [strlit "function "; f; strlit " is redeclared\n"])
      | NONE => return ();
      case SPLITP (\(f,_,_,_). f = «main») funs of
        (xs,(_,T,_,_)::ys) => error (GenErr $ strlit "main function is exported\n")
      | _ => return ();
      case SPLITP (\(_,_,ps,_). LENGTH ps > 4) $ FILTER (FST o SND) funs of
        (xs,(f,_,_,_)::ys) => error (GenErr $ concat [strlit "exported function "; f; strlit " has more than 4 arguments\n"])
      | (xs,[]) => return ();
      scope_check_funs fnames funs
    od
End


val _ = export_theory ();
