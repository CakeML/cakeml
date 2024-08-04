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

Definition scope_check_exp_def:
  scope_check_exp ctxt (Const c) = NONE ∧
  scope_check_exp ctxt (Var vname) =
    (if ¬MEM vname ctxt.vars then SOME (vname, ctxt.fname) else NONE) ∧
  scope_check_exp ctxt (Label fname) =
    (if ¬MEM fname ctxt.funcs then SOME (fname, ctxt.fname) else NONE) ∧
  scope_check_exp ctxt (Struct es) =
    scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Field index e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Load shape e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (LoadByte e) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt (Op bop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Panop pop es) = scope_check_exps ctxt es ∧
  scope_check_exp ctxt (Cmp cmp e1 e2) =
    OPTION_CHOICE
      (scope_check_exp ctxt e1)
      (scope_check_exp ctxt e2) ∧
  scope_check_exp ctxt (Shift sh e n) = scope_check_exp ctxt e ∧
  scope_check_exp ctxt BaseAddr = NONE ∧
  scope_check_exp ctxt BytesInWord = NONE ∧
  scope_check_exps ctxt [] = NONE ∧
  scope_check_exps ctxt (e::es) =
    OPTION_CHOICE (scope_check_exp ctxt e) (scope_check_exps ctxt es)
End

Definition scope_check_prog_def:
  scope_check_prog ctxt Skip = NONE ∧
  scope_check_prog ctxt (Dec v e p) =
    OPTION_CHOICE (scope_check_exp ctxt e)
                  (scope_check_prog (ctxt with vars := v :: ctxt.vars) p) ∧
  scope_check_prog ctxt (DecCall v s e args p) =
    OPTION_CHOICE
        (scope_check_exp ctxt e)
        (OPTION_CHOICE
         (scope_check_exps ctxt args)
         (scope_check_prog (ctxt with vars := v :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (Assign v e) =
    (if ¬MEM v ctxt.vars
        then SOME (v, ctxt.fname)
     else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (Store ad v) =
    OPTION_CHOICE (scope_check_exp ctxt ad)
                  (scope_check_exp ctxt v) ∧
  scope_check_prog ctxt (StoreByte dest src) =
    OPTION_CHOICE (scope_check_exp ctxt dest)
                  (scope_check_exp ctxt src) ∧
  scope_check_prog ctxt (Seq p1 p2) =
    OPTION_CHOICE (scope_check_prog ctxt p1)
                  (scope_check_prog ctxt p2) ∧
  scope_check_prog ctxt (If e p1 p2) =
    OPTION_CHOICE (scope_check_exp ctxt e)
                  (OPTION_CHOICE (scope_check_prog ctxt p1)
                                 (scope_check_prog ctxt p2)) ∧
  scope_check_prog ctxt (While e p) =
    OPTION_CHOICE (scope_check_exp ctxt e)
                  (scope_check_prog ctxt p) ∧
  scope_check_prog ctxt Break = NONE ∧
  scope_check_prog ctxt Continue = NONE ∧
  scope_check_prog ctxt (TailCall trgt args) =
    OPTION_CHOICE
      (scope_check_exp ctxt trgt)
      (scope_check_exps ctxt args) ∧
  scope_check_prog ctxt (AssignCall rt hdl trgt args) =
    OPTION_CHOICE
      (scope_check_exp ctxt trgt)
      (OPTION_CHOICE
        (scope_check_exps ctxt args)
        (if ¬MEM rt ctxt.vars
            then SOME (rt, ctxt.fname)
         else
           case hdl of
             NONE => NONE
           | SOME (eid, evar, p) =>
               if ¬MEM evar ctxt.vars
                  then SOME (evar, ctxt.fname)
               else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (StandAloneCall hdl trgt args) =
    OPTION_CHOICE
      (scope_check_exp ctxt trgt)
      (OPTION_CHOICE
        (scope_check_exps ctxt args)
        (case hdl of
             NONE => NONE
           | SOME (eid, evar, p) =>
               if ¬MEM evar ctxt.vars
                  then SOME (evar, ctxt.fname)
               else scope_check_prog (ctxt with vars := evar :: ctxt.vars) p)) ∧
  scope_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    scope_check_exps ctxt [ptr1;len1;ptr2;len2] ∧
  scope_check_prog ctxt (Raise eid excp) = scope_check_exp ctxt excp ∧
  scope_check_prog ctxt (Return rt) = scope_check_exp ctxt rt ∧
  scope_check_prog ctxt (ShMemLoad mop v e) =
    (if ¬MEM v ctxt.vars
        then SOME (v, ctxt.fname)
     else scope_check_exp ctxt e) ∧
  scope_check_prog ctxt (ShMemStore mop e1 e2) =
    OPTION_CHOICE (scope_check_exp ctxt e1)
                  (scope_check_exp ctxt e2) ∧
  scope_check_prog ctxt Tick = NONE ∧
  scope_check_prog ctxt (Annot _ _) = NONE
End

Definition scope_check_funs_def:
  scope_check_funs fnames [] = NONE ∧
  scope_check_funs fnames ((fname, _:bool, vshapes, body)::funs) =
    let ctxt = <| vars := MAP FST vshapes ; funcs := fnames ; fname := fname |> in
      OPTION_CHOICE (scope_check_prog ctxt body)
                    (scope_check_funs fnames funs)
End

(* The scope checker returns NONE to indicate that there is no scope error, and
   SOME (name, fname) to indicate that name is not in scope in an expression
   within the function fname. The first component name may be the name of a
   variable or a function. *)
Definition scope_check_def:
  scope_check funs = (scope_check_funs (MAP FST funs) funs, [""])
End


val _ = export_theory ();
