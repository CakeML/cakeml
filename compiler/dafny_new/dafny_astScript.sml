(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

Datatype:
  type = IntType
End

Datatype:
  resolvedOpcode = Lt | EqCommon | NeqCommon | Sub | Add
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
End

Datatype:
  expression =
  (* Probably for methods calls: ApplySuffix lhsResolved args *)
  | ApplySuffix expression (expression list)
  | IdentifierExpr string type
  | BinaryExpr resolvedOpcode expression expression
  | LiteralExpr literal
  (* MemberSelectExpr obj memberName *)
  | MemberSelectExpr expression string
End

Datatype:
  assignmentRhs = ExprRhs expression
End

Datatype:
  concrete_assign_statement = Assignment (expression list) (assignmentRhs list);
  block_stmt = BlockStmt (statement list);
  statement =
  | Statement_ConreteAssignStatement concrete_assign_statement
  | If expression block_stmt (statement option)
  (* VarDecl locals assign *)
  | VarDecl (localVariable list) (concrete_assign_statement option)
  | While expression block_stmt
  | Statement_BlockStmt block_stmt
  | PrintStmt (expression list);
End

Datatype:
  member_decl =
  (* Method name ins outs body *)
  Method string (formal list) (formal list) block_stmt
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
