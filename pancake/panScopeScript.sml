(*
  Scope checking for Pancake.
*)

open preamble errorLogMonadTheory panLangTheory;

val _ = new_theory "panScope";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "errorLog";

Datatype:
  context = <| vars : varname list ;
               funcs : funname list ;
               fname : funname |>
End

Datatype:
  unbound = UnbVar varname funname
          | UnbFunc funname funname
End

(* ???
Type static_result = ``:('a, unbound) error # mlstring list``
*)

Definition scope_check_exp_def:
  scope_check_exp ctxt (Const c) = return () ∧
  scope_check_exp ctxt (Var vname) =
    (if ¬MEM vname ctxt.vars then error (UnbVar vname ctxt.fname) else return ()) ∧
  scope_check_exp ctxt (Label fname) =
    (if ¬MEM fname ctxt.funcs then error (UnbFunc fname ctxt.fname) else return ()) ∧
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
  scope_check_prog ctxt Skip = return () ∧
  scope_check_prog ctxt (Dec v e p) =
    do
      scope_check_exp ctxt e;
      scope_check_prog (ctxt with vars := v :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (DecCall v s e args p) =
    do
      scope_check_exp ctxt e;
      scope_check_exps ctxt args;
      scope_check_prog (ctxt with vars := v :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (Assign v e) =
    (if ¬MEM v ctxt.vars
        then error (UnbVar v ctxt.fname)
    else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (Store ad v) =
    do
      scope_check_exp ctxt ad;
      scope_check_exp ctxt v
    od ∧
  scope_check_prog ctxt (StoreByte dest src) =
    do
      scope_check_exp ctxt dest;
      scope_check_exp ctxt src
    od ∧
  scope_check_prog ctxt (Seq p1 p2) =
    do
      scope_check_prog ctxt p1;
      scope_check_prog ctxt p2
    od ∧
  scope_check_prog ctxt (If e p1 p2) =
    do
      scope_check_exp ctxt e;
      scope_check_prog ctxt p1;
      scope_check_prog ctxt p2
    od ∧
  scope_check_prog ctxt (While e p) =
    do
      scope_check_exp ctxt e;
      scope_check_prog ctxt p
    od ∧
  scope_check_prog ctxt Break = return () ∧
  scope_check_prog ctxt Continue = return () ∧
  scope_check_prog ctxt (TailCall trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args
    od ∧
  scope_check_prog ctxt (AssignCall rt hdl trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args;
      if ¬MEM rt ctxt.vars
        then error (UnbVar rt ctxt.fname)
      else
        case hdl of
          NONE => return ()
        | SOME (eid, evar, p) =>
            if ¬MEM evar ctxt.vars
              then error (UnbVar evar ctxt.fname)
            else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (StandAloneCall hdl trgt args) =
    do
      scope_check_exp ctxt trgt;
      scope_check_exps ctxt args;
      case hdl of
        NONE => return ()
      | SOME (eid, evar, p) =>
          if ¬MEM evar ctxt.vars
            then error (UnbVar evar ctxt.fname)
          else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p
    od ∧
  scope_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    scope_check_exps ctxt [ptr1;len1;ptr2;len2] ∧
  scope_check_prog ctxt (Raise eid excp) = scope_check_exp ctxt excp ∧
  scope_check_prog ctxt (Return rt) = scope_check_exp ctxt rt ∧
  scope_check_prog ctxt (ShMemLoad mop v e) =
    (if ¬MEM v ctxt.vars
      then error (UnbVar v ctxt.fname)
    else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (ShMemStore mop e1 e2) =
    do
      scope_check_exp ctxt e1;
      scope_check_exp ctxt e2
    od ∧
  scope_check_prog ctxt Tick = return () ∧
  scope_check_prog ctxt (Annot _ _) = return ()
End

Definition scope_check_funs_def:
  scope_check_funs fnames [] = return () ∧
  scope_check_funs fnames ((fname, _:bool, vshapes, body)::funs) =
    let ctxt = <| vars := MAP FST vshapes ; funcs := fnames ; fname := fname |> in
      do
        scope_check_prog ctxt body;
        scope_check_funs fnames funs
      od
End

(* The scope checker returns StatSuccess () to indicate that there is no scope error, and
   StatFailure (name, fname) to indicate that name is not in scope in an expression
   within the function fname. The first component name may be the name of a
   variable or a function. *)
Definition scope_check_def:
  scope_check funs = scope_check_funs (MAP FST funs) funs
End


val _ = export_theory ();
