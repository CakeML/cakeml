(*
  A parser for CP problems based on sexpressions
*)
Theory cp_parse
Libs
  preamble
Ancestors
  cp dafny_sexp result_monad

(* INL: error message, INR: parsed sexpression *)
Definition lexparse_def:
  lexparse s =
    bind (lex (explode s)) parse
End

(*
  Tentatively, we will have everything live in a big s-expression with
    either 2 or 3 elements.

(
  // the first element is a list of all the bounds
  (
    (...)
    (...)
    (...)
  )
  // the second one is a list of all the constraints
  (
    (...)
    (...)
    (...)
  )
  // the third (if it exists) indicates the variable to minimize/maximize
  (min x) | (max x)
)
*)

Definition sexp_bnd_def:
  sexp_bnd e =
    case e of
      Expr [Atom v; Atom lb; Atom ub] =>
        (case (fromString lb, fromString ub) of
          (SOME lb, SOME ub) => return (v,lb,ub)
        | _ => fail (strlit "unable to parse integer bounds"))
    | _ => fail (strlit "invalid bound sexpression")
End

Definition sexp_bnds_def:
  (sexp_bnds [] = return []) ∧
  (sexp_bnds (e::es) =
    do
      x <- sexp_bnd e;
      xs <- sexp_bnds es;
      return (x::xs)
    od)
End

Definition sexp_varc_def:
  (sexp_varc (Atom v) =
  case fromString v of
    NONE => return (INL v)
  | SOME i => return ((INR i):mlstring varc)) ∧
  (sexp_varc _ =
    fail (strlit "invalid sexpression at var/const position"))
End

Definition sexp_varcs_def:
  (sexp_varcs [] = return []) ∧
  (sexp_varcs (e::es) =
     do
      x <- sexp_varc e;
      xs <- sexp_varcs es;
      return (x::xs)
    od)
End

Definition sexp_not_equals_def:
  sexp_not_equals rest =
  do
    lss <- sexp_varcs rest;
    (case lss of
      [xx;yy] => return (NotEquals xx yy)
    | _ => fail (strlit "incorrect number of arguments to not-equals"))
  od
End

Definition sexp_all_different_def:
  sexp_all_different rest =
  do
    lss <- sexp_varcs rest;
    return (AllDifferent lss)
  od
End

Definition sexp_constraint_dispatch_def:
  sexp_constraint_dispatch name rest =
  if name = strlit "not-equals" then sexp_not_equals rest
  else if name = strlit "all-different" then sexp_all_different rest
  else
    fail (strlit "unsupported constraint: " ^ name)
End

Definition sexp_constraint_def:
  sexp_constraint e =
  case e of
    Expr (Atom name::rest) =>
    sexp_constraint_dispatch name rest
  | _ => fail (strlit "invalid constraint sexpression")
End

Definition sexp_constraints_def:
  (sexp_constraints [] = return []) ∧
  (sexp_constraints (e::es) =
    do
      x <- sexp_constraint e;
      xs <- sexp_constraints es;
      return (x::xs)
    od)
End

Definition sexp_obj_def:
  (sexp_obj [] = return NoObjective) ∧
  (sexp_obj [Atom x;Atom y] =
    if x = strlit "minimize"
    then return (Minimize y)
    else
    if x = strlit "maximize"
    then return (Maximize y)
    else fail (strlit "invalid objective sexpression")) ∧
  (sexp_obj _ = fail (strlit "invalid objective sexpression"))
End

Definition sexp_cp_inst_def:
  sexp_cp_inst e =
  case e of
    Expr (Expr bnds::Expr constraints::mopt) =>
    do
      bb <- sexp_bnds bnds;
      cs <- sexp_constraints constraints;
      obj <- sexp_obj mopt;
      return ((bb,cs,obj):cp_inst)
    od
  | _ => fail (strlit "invalid sexpression for top-level CP instance")
End

(*

EVAL``
bind (lexparse
(
concat
[strlit"(";
  concat
  [strlit"(";
    strlit"(X 10 25)";
    strlit"(Y 1 20)";
    strlit"(Z -100 200)";
  strlit")"];
  concat
  [strlit"(";
    strlit"(not-equals Y Z)";
    strlit"(not-equals X 15)";
    strlit"(not-equals 14 15)";
    strlit"(all-different X Y Z)";
  strlit")"];
strlit")"]))
sexp_cp_inst``

*)
