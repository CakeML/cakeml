(*
  Definitions to convert Dafny's AST into CakeML's AST.
*)

open preamble
open astTheory  (* CakeML AST *)
open dafnyAstTheory

val _ = new_theory "toCakeMlAst";

val hello_dast = EVAL “sexp_program ⟪SX_SYM "Program";
         ⟪ ⟪SX_SYM "Module.Module"; ⟪SX_SYM "Name.Name"; SX_STR "_System"⟫;
         ⟪ ⟫;
         ⟪SX_SYM "Some";
         ⟪ ⟪SX_SYM "ModuleItem.Newtype";
         ⟪SX_SYM "Newtype.Newtype"; ⟪SX_SYM "Name.Name"; SX_STR "nat"⟫; ⟪ ⟫;
         ⟪SX_SYM "Type.Primitive"; ⟪SX_SYM "Primitive.Int"⟫ ⟫;
         ⟪SX_SYM "NewtypeRange.NoRange"⟫; ⟪ ⟫; ⟪SX_SYM "None"⟫;
         ⟪ ⟪SX_SYM "Attribute.Attribute"; SX_STR "axiom"; ⟪ ⟫ ⟫ ⟫ ⟫ ⟫;
         ⟪SX_SYM "ModuleItem.Datatype";
         ⟪SX_SYM "Datatype.Datatype"; ⟪SX_SYM "Name.Name"; SX_STR "Tuple2"⟫;
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "_System"⟫ ⟫;
         ⟪ ⟪SX_SYM "TypeArgDecl.TypeArgDecl";
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "T0"⟫ ⟫; ⟪ ⟫ ⟫;
         ⟪SX_SYM "TypeArgDecl.TypeArgDecl";
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "T1"⟫ ⟫; ⟪ ⟫ ⟫ ⟫;
         ⟪ ⟪SX_SYM "DatatypeCtor.DatatypeCtor";
         ⟪SX_SYM "Name.Name"; SX_STR "___hMake2"⟫;
         ⟪ ⟪SX_SYM "DatatypeDtor.DatatypeDtor";
         ⟪SX_SYM "Formal.Formal"; ⟪SX_SYM "Name.Name"; SX_STR "_0"⟫;
         ⟪SX_SYM "Type.TypeArg";
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "T0"⟫ ⟫ ⟫; ⟪ ⟫ ⟫;
         ⟪SX_SYM "Some"; SX_STR "_0"⟫ ⟫;
         ⟪SX_SYM "DatatypeDtor.DatatypeDtor";
         ⟪SX_SYM "Formal.Formal"; ⟪SX_SYM "Name.Name"; SX_STR "_1"⟫;
         ⟪SX_SYM "Type.TypeArg";
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "T1"⟫ ⟫ ⟫; ⟪ ⟫ ⟫;
         ⟪SX_SYM "Some"; SX_STR "_1"⟫ ⟫ ⟫; SX_SYM "true"⟫ ⟫; ⟪ ⟫;
         SX_SYM "false"; ⟪ ⟫ ⟫ ⟫;
         ⟪SX_SYM "ModuleItem.Datatype";
         ⟪SX_SYM "Datatype.Datatype"; ⟪SX_SYM "Name.Name"; SX_STR "Tuple0"⟫;
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "_System"⟫ ⟫;
         ⟪ ⟫;
         ⟪ ⟪SX_SYM "DatatypeCtor.DatatypeCtor";
         ⟪SX_SYM "Name.Name"; SX_STR "___hMake0"⟫; ⟪ ⟫; SX_SYM "false"⟫ ⟫;
         ⟪ ⟫; SX_SYM "false"; ⟪ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫;
         ⟪SX_SYM "Module.Module"; ⟪SX_SYM "Name.Name"; SX_STR "_module"⟫;
         ⟪ ⟫;
         ⟪SX_SYM "Some";
         ⟪ ⟪SX_SYM "ModuleItem.Class";
         ⟪SX_SYM "Class.Class"; ⟪SX_SYM "Name.Name"; SX_STR "__default"⟫;
         ⟪SX_SYM "Ident.Ident"; ⟪SX_SYM "Name.Name"; SX_STR "_module"⟫ ⟫;
         ⟪ ⟫; ⟪ ⟫; ⟪ ⟫;
         ⟪ ⟪SX_SYM "ClassItem.Method";
         ⟪SX_SYM "Method.Method"; SX_SYM "true"; SX_SYM "true";
         ⟪SX_SYM "None"⟫; ⟪SX_SYM "Name.Name"; SX_STR "Main"⟫; ⟪ ⟫; ⟪ ⟫;
         ⟪ ⟪SX_SYM "Statement.Print";
         ⟪SX_SYM "Expression.Literal";
         ⟪SX_SYM "Literal.StringLiteral"; SX_STR "Hello, World";
         SX_SYM "false"⟫ ⟫ ⟫; ⟪SX_SYM "Statement.EarlyReturn"⟫ ⟫; ⟪ ⟫;
         ⟪SX_SYM "Some"; ⟪ ⟫ ⟫ ⟫ ⟫ ⟫; ⟪ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫ ⟫”;

val _ = export_theory();
