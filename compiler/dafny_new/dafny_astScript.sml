(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

Datatype:
  type =
  | IntType
  | BoolType
  | UserDefinedType string
End

Datatype:
  resolvedOpcode =
  Lt | EqCommon | NeqCommon | Sub | Add | Div
End

Datatype:
  formal =
  (* Formal name type *)
  Formal string type
End

Datatype:
  localVariable = LocalVariable string type
End

Datatype:
  literal =
  (* StringLiteral isVerbatim value *)
  | StringLiteral bool string
  | Null
  | BigInteger int
  | BoolV bool
End

Datatype:
  expression =
  (* MethodCall name args *)
  | MethodCall string (expression list)
  (* FunctionCall name args *)
  | FunctionCall string (expression list)
  | IdentifierExpr string type
  | BinaryExpr resolvedOpcode expression expression
  | LiteralExpr literal
  | ArrayLen expression
  (* ArraySelect arr idx *)
  | ArraySelect expression expression
  (* ITE test thn els *)
  | ITE expression expression expression
End

Datatype:
  assignmentRhs =
  | ExprRhs expression
  (* AllocateArray explicitType arrayDimensions elementInit initDisplay
     - At most one of elementInit and initDisplay may be non-null
     - initDisplay is a "sequence display" expression, e.g. [4+2, 1+5, a*b]
     - initDisplay seems to be only used for one-dimensional array *)
  | AllocateArray type (expression list) (expression option) ((expression list) option)
End

Datatype:
  statement =
  | Skip
  | Then statement statement
  | Assignment (expression list) (assignmentRhs list)
  | If expression statement statement
  (* VarDecl locals assign scope *)
  | VarDecl (localVariable list) statement statement
  | While expression statement
  | PrintStmt (expression list)
  | ReturnStmt ((assignmentRhs list) option);
End

Datatype:
  member_decl =
  (* Method name ins outs body *)
  | Method string (formal list) (formal list) block_stmt
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
