(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble
open mlstringTheory

val _ = new_theory "dafny_ast";

Datatype:
  type =
  | BoolT
  | IntT
  | StrT
  | ArrT type
End

Datatype:
  un_op = Not
End

Datatype:
  bin_op = Lt | Le | Ge | Eq | Neq | Sub | Add | Mul | And | Or | Imp | Div
End

Datatype:
  lit =
  | BoolL bool
  | IntL int
  | StrL mlstring
End

Datatype:
  exp =
  | Lit lit
  | Var mlstring
  (* Exp_If test thn els *)
  | Exp_If exp exp exp
  | UnOp un_op exp
  | BinOp bin_op exp exp
  (* ArrLen arr *)
  | ArrLen exp
  (* ArrSel arr idx *)
  | ArrSel exp exp
  (* FunCall name args *)
  | FunCall mlstring (exp list)
  (* Forall var term *)
  | Forall (mlstring # type) exp
End

Overload If = “Exp_If”

Datatype:
  lhs_exp =
  | VarLhs mlstring
  (* ArrSelLhs arr idx *)
  | ArrSelLhs exp exp
End

(* https://dafny.org/dafny/DafnyRef/DafnyRef#sec-rhs-expression
   Our definition of rhs_exp does not quite match the one described in the
   reference, as method calls appear to be special (since they may result in
   multiple values) *)
Datatype:
  rhs_exp =
  | ExpRhs exp
  (* ArrAlloc length init_value *)
  | ArrAlloc exp exp
End

Datatype:
  statement =
  | Skip
  | Assert exp
  | Then statement statement
  | If exp statement statement
  (* Dec local scope
     - scope also contains possible assignments *)
  | Dec (mlstring # type) statement
  | Assign (lhs_exp list) (rhs_exp list)
  (* While guard invariants decreases mod body *)
  | While exp (exp list) (exp list) (exp list) statement
  | Print ((exp # type) list)
  (* MetCall lhss name args
     - Results of a method call must always be bound to something, hence lhss *)
  | MetCall (lhs_exp list) mlstring (exp list)
  | Return
End

Datatype:
  member_decl =
  (* Method name ins req ens reads
            decreases outs mod body *)
  | Method mlstring ((mlstring # type) list) (exp list) (exp list) (exp list)
           (exp list) ((mlstring # type) list) (exp list) statement
  (* Function name ins result_type req reads
              decreases body *)
  | Function mlstring ((mlstring # type) list) type (exp list) (exp list)
             (exp list) exp
End

Datatype:
  (* For now, we only consider programs with a single module that use the
     default class *)
  program = Program (member_decl list)
End

val _ = export_theory ();
