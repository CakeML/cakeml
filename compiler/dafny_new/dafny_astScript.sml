(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble
open mlstringTheory

val _ = new_theory "dafny_ast";

(* TODO Start with easy cases *)

Datatype:
  type =
  | IntT
  | BoolT
  | StringT
  | ArrayT type
End

Datatype:
  binary_op = Lt | Le | Ge | Eq | Neq | Sub | Add | Mul | Div | And | Imp | Or
End

Datatype:
  literal =
  | IntLit int
  | BoolLit bool
  | StringLit mlstring
End

Datatype:
  expression =
  (* FunctionCall name args *)
  | FunctionCall mlstring (expression list)
  | IdentifierExp mlstring type
  | BinaryExp binary_op expression expression
  | LiteralExp literal
  | ArrayLen expression
  (* ArraySelect arr idx *)
  | ArraySelect expression expression
  (* ITE test thn els *)
  | ITE expression expression expression
  (* ForallExp boundVar term *)
  (* TODO Fix in C# *)
  | ForallExp (mlstring # type) expression
End

(* https://dafny.org/dafny/DafnyRef/DafnyRef#sec-rhs-expression
   Our definition of rhs_exp does not quite match the one described in the
   reference, as method calls appear to be special (since they may result in
   multiple values) *)
Datatype:
  rhs_exp =
  | ExpRhs expression
  (* AllocArray type length initValue *)
  | AllocArray type expression expression
End

Datatype:
  statement =
  | Skip
  | Then statement statement
  | Assign (expression list) (rhs_exp list)
  | If expression statement statement
  (* MetCall lhss name args
     - Results of a method call must always be bound to something, hence lhss *)
  | MetCall (expression list) mlstring (expression list)
  (* Dec locals scope
     - scope also contains possible assignments *)
  | Dec ((mlstring # type) list) statement
  (* While guard invariants decreases mod
           body *)
  | While expression (expression list) (expression list) (expression list)
          statement
  | Print ((expression # type) list)
  | Return
  | Assert expression
End

Datatype:
  member_decl =
  (* Method name ins req ens
            reads decreases outs
            mod body *)
  | Method mlstring ((mlstring # type) list) (expression list) (expression list)
           (expression list) (expression list) ((mlstring # type) list)
           (expression list) statement
  (* Function name ins resultType req
              reads body *)
  | Function mlstring ((mlstring # type) list) type (expression list)
             (expression list) expression
End

Datatype:
  (* For now, we only consider programs with a single module that uses the
     default class *)
  program = Program (member_decl list)
End

val _ = export_theory ();
