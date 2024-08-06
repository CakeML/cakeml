(*
  Scope checking for Pancake.
*)

open preamble panLangTheory;

val _ = new_theory "panScope";


Datatype:
  context = <| vars : varname list ;
               funcs : funname list ;
               fname : funname |>
End

Datatype:
  unbound = UnbVar varname funname
          | UnbFunc funname funname
End

Datatype:
  statres = StatSuccess 'a (string list)
          | StatFailure unbound (string list)
End

Definition result_choice_def:
  result_choice a b =
    case a of
      (StatFailure unbA wsA) => a
    | (StatSuccess shA wsA) =>
        case b of
          (StatFailure unbB wsB) => (StatFailure unbB (wsA ++ wsB))
        | (StatSuccess shB wsB) => (StatSuccess shB (wsA ++ wsB))
End

Definition scope_check_exp_def:
  scope_check_exp ctxt (Const c) = (StatSuccess () []) ∧
  scope_check_exp ctxt (Var vname) =
    (if ¬MEM vname ctxt.vars then StatFailure (UnbVar vname ctxt.fname) [] else StatSuccess () []) ∧
  scope_check_exp ctxt (Label fname) =
    (if ¬MEM fname ctxt.funcs then StatFailure (UnbFunc fname ctxt.fname) [] else StatSuccess () []) ∧
  scope_check_exp ctxt (Struct es) =
    scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Field index e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Load shape e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (LoadByte e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Op bop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Panop pop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Cmp cmp e1 e2) =
    result_choice
      (scope_check_exp ctxt e1)
      (scope_check_exp ctxt e2) ∧
  scope_check_exp ctxt (Shift sh e n) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt BaseAddr = (StatSuccess () []) ∧
  scope_check_exp ctxt BytesInWord = (StatSuccess () []) ∧
  scope_check_exps ctxt [] = (StatSuccess () []) ∧
  scope_check_exps ctxt (e::es) =
    result_choice (scope_check_exp ctxt e) (scope_check_exps ctxt es)
End

Definition scope_check_prog_def:
  scope_check_prog ctxt Skip = (StatSuccess () []) ∧
  scope_check_prog ctxt (Dec v e p) =
    result_choice (scope_check_exp ctxt e)
                  (scope_check_prog (ctxt with vars := v :: ctxt.vars) p) ∧
  scope_check_prog ctxt (DecCall v s e args p) =
    result_choice
        (scope_check_exp ctxt e)
        (result_choice
         (scope_check_exps ctxt args)
         (scope_check_prog (ctxt with vars := v :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (Assign v e) =
    (if ¬MEM v ctxt.vars
        then (StatFailure (UnbVar v ctxt.fname) [])
     else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (Store ad v) =
    result_choice (scope_check_exp ctxt ad)
                  (scope_check_exp ctxt v) ∧
  scope_check_prog ctxt (StoreByte dest src) =
    result_choice (scope_check_exp ctxt dest)
                  (scope_check_exp ctxt src) ∧
  scope_check_prog ctxt (Seq p1 p2) =
    result_choice (scope_check_prog ctxt p1)
                  (scope_check_prog ctxt p2) ∧
  scope_check_prog ctxt (If e p1 p2) =
    result_choice (scope_check_exp ctxt e)
                  (result_choice (scope_check_prog ctxt p1)
                                 (scope_check_prog ctxt p2)) ∧
  scope_check_prog ctxt (While e p) =
    result_choice (scope_check_exp ctxt e)
                  (scope_check_prog ctxt p) ∧
  scope_check_prog ctxt Break = (StatSuccess () []) ∧
  scope_check_prog ctxt Continue = (StatSuccess () []) ∧
  scope_check_prog ctxt (TailCall trgt args) =
    result_choice
      (scope_check_exp ctxt trgt)
      (scope_check_exps ctxt args) ∧
  scope_check_prog ctxt (AssignCall rt hdl trgt args) =
    result_choice
      (scope_check_exp ctxt trgt)
      (result_choice
        (scope_check_exps ctxt args)
        (if ¬MEM rt ctxt.vars
            then (StatFailure (UnbVar rt ctxt.fname) [])
         else
           case hdl of
             NONE => (StatSuccess () [])
           | SOME (eid, evar, p) =>
               if ¬MEM evar ctxt.vars
                  then (StatFailure (UnbVar evar ctxt.fname) [])
               else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (StandAloneCall hdl trgt args) =
    result_choice
      (scope_check_exp ctxt trgt)
      (result_choice
        (scope_check_exps ctxt args)
        (case hdl of
             NONE => (StatSuccess () [])
           | SOME (eid, evar, p) =>
               if ¬MEM evar ctxt.vars
                  then (StatFailure (UnbVar evar ctxt.fname) [])
               else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    scope_check_exps ctxt [ptr1;len1;ptr2;len2] ∧
  scope_check_prog ctxt (Raise eid excp) = scope_check_exp ctxt excp ∧
  scope_check_prog ctxt (Return rt) = scope_check_exp ctxt rt ∧
  scope_check_prog ctxt (ShMemLoad mop v e) =
    (if ¬MEM v ctxt.vars
        then (StatFailure (UnbVar v ctxt.fname) [])
     else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (ShMemStore mop e1 e2) =
    result_choice (scope_check_exp ctxt e1)
                  (scope_check_exp ctxt e2) ∧
  scope_check_prog ctxt Tick = (StatSuccess () []) ∧
  scope_check_prog ctxt (Annot _ _) = (StatSuccess () [])
End

Definition scope_check_funs_def:
  scope_check_funs fnames [] = (StatSuccess () []) ∧
  scope_check_funs fnames ((fname, _:bool, vshapes, body)::funs) =
    let ctxt = <| vars := MAP FST vshapes ; funcs := fnames ; fname := fname |> in
      result_choice (scope_check_prog ctxt body)
                    (scope_check_funs fnames funs)
End

(* The scope checker returns StatSuccess () to indicate that there is no scope error, and
   StatFailure (name, fname) to indicate that name is not in scope in an expression
   within the function fname. The first component name may be the name of a
   variable or a function. *)
Definition scope_check_def:
  scope_check funs = scope_check_funs (MAP FST funs) funs
End


val _ = export_theory ();
