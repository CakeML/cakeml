(*
  Abstract Syntax Tree for a subset of Dafny.
*)

open preamble

val _ = new_theory "dafny_ast";

Datatype:
  type =
  | IntType
  | UserDefinedType string
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
  (* ApplySuffix lhsResolved args
     - Probably for methods calls *)
  | ApplySuffix expression (expression list)
  | IdentifierExpr string type
  | BinaryExpr resolvedOpcode expression expression
  | LiteralExpr literal
  (* MemberSelectExpr obj memberName *)
  | MemberSelectExpr expression string
  (* SeqSelectExpr selectOne seq e0 e1
     - ¬selectOne ==> select a range *)
  | SeqSelectExpr bool expression expression (expression option)
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
