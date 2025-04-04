(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

Datatype:
  type =
  | IntT
  | BoolT
  | ArrayT type
End

Datatype:
  bop = Lt | Eq | Neq | Sub | Add | Div
End

Datatype:
  (* Formal name type *)
  formal = Formal string type
End

Datatype:
  local_var = LocalVar string type
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
  | VarDecl (local_var list) statement statement
  | While expression statement
  | Print (expression list)
  | Return ((assign_rhs list) option);
End

Datatype:
  member_decl =
  (* Method name ins outs body *)
  | Method string (formal list) (formal list) statement
  (* Function name ins resultType body *)
  | Function string (formal list) type expression
End

Datatype:
  top_level_decl =
  (* DefaultClassDecl name members *)
  DefaultClassDecl string (member_decl list)
End

Datatype:
  module_definition =
  (* Module string topLevelDecls *)
  Module string (top_level_decl list)
End

Datatype:
  program =
  (* Program compileModules *)
  Program (module_definition list)
End
