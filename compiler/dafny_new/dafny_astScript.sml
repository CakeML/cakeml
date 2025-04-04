(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

(* TODO Add ghost code *)
(* TODO Make sure to have assert? *)

Datatype:
  type =
  | IntT
  | BoolT
  | ArrayT type
End

Datatype:
  bop = Lt | Le | Ge | Eq | Neq | Sub | Add | Mul | Div | And | Imp
End

Datatype:
  literal =
  | IntV int
  | BoolV bool
  (* StringV isVerbatim value *)
  | StringV bool string
End

Datatype:
  expression =
  (* MethodCall name args *)
  | MethodCall string (expression list)
  (* FunctionCall name args *)
  | FunctionCall string (expression list)
  | IdentifierExp string type
  | BinaryExp bop expression expression
  | LiteralExp literal
  | ArrayLen expression
  (* ArraySelect arr idx *)
  | ArraySelect expression expression
  (* ITE test thn els *)
  | ITE expression expression expression
  (* ForallExp boundVars term *)
  | ForallExp (string # type) expression
End

Datatype:
  assign_rhs =
  | ExpRhs expression
  (* AllocArray type length initValue *)
  | AllocArray type expression expression
End

Datatype:
  statement =
  | Skip
  | Then statement statement
  | Assign (expression list) (assign_rhs list)
  | If expression statement statement
  (* VarDecl locals assign scope *)
  | VarDecl ((string # type) list) statement statement
  (* While guard invariants decreases mod
           body *)
  | While expression (expression list) (expression list) (expression list)
          statement
  | Print (expression list)
  | Return (assign_rhs list)
  | Assert expression
End

Datatype:
  member_decl =
  (* Method name ins req ens
            reads decreases outs
            mod body *)
  | Method string ((string # type) list) (expression list) (expression list)
           (expression list) (expression list) ((string # type) list)
           (expression list) statement
  (* Function name ins resultType req
              reads body *)
  | Function string ((string # type) list) type (expression list)
             (expression list) expression
End

Datatype:
  (* For now, we only consider programs with a single module that uses the
     default class *)
  program = Program (member_decl list)
End

val _ = export_theory ();
