(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

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
  | StringLit string
End

Datatype:
  expression =
  (* FunctionCall name args *)
  | FunctionCall string (expression list)
  | IdentifierExp string type
  | BinaryExp binary_op expression expression
  | LiteralExp literal
  | ArrayLen expression
  (* ArraySelect arr idx *)
  | ArraySelect expression expression
  (* ITE test thn els *)
  | ITE expression expression expression
  (* ForallExp boundVars term *)
  | ForallExp (string # type) expression
End

(* https://dafny.org/dafny/DafnyRef/DafnyRef#sec-rhs-expression *)
Datatype:
  rhs_exp =
  | ExpRhs expression
  (* MethodCall name args *)
  | MethodCall string (expression list)
  (* AllocArray type length initValue *)
  | AllocArray type expression expression
End

Datatype:
  statement =
  | Skip
  | Then statement statement
  | Assign (expression list) (rhs_exp list)
  | If expression statement statement
  (* TODO? Can this be simplified? *)
  (* VarDecl locals assign scope *)
  | VarDecl ((string # type) list) statement statement
  (* While guard invariants decreases mod
           body *)
  | While expression (expression list) (expression list) (expression list)
          statement
  | Print ((expression # type) list)
  | Return (rhs_exp list)
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
