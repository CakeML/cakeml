(*
  Definition of Dafny abstract syntax (AST).
*)

open preamble

val _ = new_theory "dafny_ast";

Datatype:
  name =
  | Name string
End

Datatype:
  ident =
  | Ident name
End

Datatype:
  attribute =
  (* Attribute name args *)
  | Attribute string (string list)
End

Datatype:
  primitive =
  | Int
  | Real
  | String
  | Bool
  | Char
End

Datatype:
  collKind =
  | CollKind_Seq
  | CollKind_Array
  | CollKind_Map
End

Datatype:
  typeArgBound =
  | SupportsEquality
  | SupportsDefault
End

Datatype:
  typeArgDecl =
  (* TypeArgDecl name bounds *)
  | TypeArgDecl ident (typeArgBound list)
End

Datatype:
  newtypeRange =
  | U8 | I8
  | U16 | I16
  | U32 | I32
  | U64 | I64
  | U128 | I128
  | BigInt | NoRange
End

Datatype:
  unaryOp =
  | Not | BitwiseNot
  | Cardinality
End

Datatype:
  binOp =
  (* Eq referential nullable *)
  | Eq bool bool
  | Div | EuclidianDiv
  | Mod | EuclidianMod
  (* a ≤ b is !(b < a) *)
  | Lt | LtChar
  | Plus | Minus | Times
  | BitwiseAnd | BitwiseOr | BitwiseXor
  | BitwiseShiftRight | BitwiseShiftLeft
  | And | Or
  | In
  | SeqProperPrefix | SeqPrefix
  | SetMerge | SetSubtraction | SetIntersection
  | Subset | ProperSubset | SetDisjoint
  | MapMerge | MapSubtraction
  | MultisetMerge | MultisetSubtraction | MultisetIntersection
  | Submultiset | ProperSubmultiset | MultisetDisjoint
  | Concat
  | BinOp_Passthrough string
End

Datatype:
  datatypeType =
  (* DatatypeType path attributes *)
  | DatatypeType (ident list) (attribute list)
End

Datatype:
  resolvedType =
  | ResolvedType_Datatype datatypeType
  (* Trait path attributes *)
  | ResolvedType_Trait (ident list) (attribute list)
  (* Newtype baseType range erase attributes *)
  | ResolvedType_Newtype type newtypeRange bool (attribute list) ;

  type =
  (* Path idents typeArgs resolved *)
  | Path (ident list) (type list) resolvedType
  | Nullable type
  | Tuple (type list)
  (* Array element dims *)
  | Array type num
  | Seq type
  | Set type
  | Multiset type
  (* Map key value *)
  | Map type type
  | SetBuilder type
  (* MapBuilder key value *)
  | MapBuilder type type
  (* Arrow args result *)
  | Arrow (type list) type
  | Primitive primitive | Passthrough string
  | TypeArg ident
End

Datatype:
  literal =
  | BoolLiteral bool
  | IntLiteral string type
  | DecLiteral string string type
  (* StringLiteral str verbatim *)
  | StringLiteral string bool
  | CharLiteral char
  | CharLiteralUTF16 num
  | Null type
End

Datatype:
  formal =
  | Formal name type (attribute list)
End

Datatype:
  callSignature =
  (* CallSignature parameters *)
  | CallSignature (formal list)
End

Datatype:
  callName =
  (* CallName name onType signature *)
  | CallName name (type option) callSignature
  | MapBuilderAdd
  | MapBuilderBuild
  | SetBuilderAdd
  | SetBuilderBuild
End

Datatype:
  assignLhs =
  | AssignLhs_Ident ident
  (* Select expr field *)
  | AssignLhs_Select expression name
  (* Index expr indices *)
  | AssignLhs_Index expression (expression list) ;

  expression =
  | Literal literal
  | Expression_Ident name
  | Companion (ident list)
  | Expression_Tuple (expression list)
  (* New path typeArgs args *)
  | New (ident list) (type list) (expression list)
  (* NewArray dims typ *)
  | NewArray (expression list) type
  (* DatatypeValue datatypeType typeArgs variant isCo contents *)
  | DatatypeValue datatypeType (type list) name bool
                  ((string # expression) list)
  (* Convert value from type *)
  | Convert expression type type
  (* SeqConstruct length elem *)
  | SeqConstruct expression expression
  | SeqValue (expression list) type
  | SetValue (expression list)
  | MultisetValue (expression list)
  | MapValue ((expression # expression) list)
  (* MapBuilder keyType valueType *)
  | Expression_MapBuilder type type
  (* SeqUpdate expr indexExpr value *)
  | SeqUpdate expression expression expression
  (* MapUpdate expr indexExpr value *)
  | MapUpdate expression expression expression
  (* SetBuilder elemType *)
  | Expression_SetBuilder type
  | ToMultiset expression
  | This
  (* Ite cond thn els *)
  | Ite expression expression expression
  (* In contract to Dafny, we do not include formatting information *)
  | UnOp unaryOp expression
  (* BinOp op left right *)
  | BinOp binOp expression expression
  (* ArrayLen expr dim *)
  | ArrayLen expression num
  | MapKeys expression
  | MapValues expression
  (* Select expr field isConstant onDatatype fieldType *)
  | Select expression name bool bool type
  (* SelectFn expr field onDatatype isStatic arity *)
  | SelectFn expression name bool bool num
  (* Index expr collKind indices *)
  | Index expression collKind (expression list)
  (* IndexRange expr isArray low high *)
  | IndexRange expression bool (expression option) (expression option)
  (* TupleSelect expr index fieldType *)
  | TupleSelect expression num type
  (* Call on callName typeArgs args *)
  | Expression_Call expression callName (type list) (expression list)
  (* Lambda params retType body *)
  | Lambda (formal list) type (statement list)
  (* BetaRedex values retType expr *)
  | BetaRedex ((formal # expression) list) type expression
  (* IIFE name typ value iifeBody *)
  | IIFE ident type expression expression
  (* Apply expr args *)
  | Apply expression (expression list)
  (* TypeTest on dType variant *)
  | TypeTest expression (ident list) name
  | InitializationValue type
  | BoolBoundedPool
  (* SetBoundedPool of *)
  | SetBoundedPool expression
  (* SeqBoundedPool of includeDuplicates *)
  | SeqBoundedPool expression bool
  (* IntRange lo hi *)
  | IntRange expression expression ;

  statement =
  | DeclareVar name type (expression option)
  | Assign assignLhs expression
  (* If cond thn els *)
  | If expression (statement list) (statement list)
  (* Labeled lbl body *)
  | Labeled string (statement list)
  | While expression (statement list)
  (* Foreach boundName boundType over body *)
  | Foreach name type expression (statement list)
  (* Call on callName typeArgs args outs *)
  | Call expression callName (type list) (expression list)
         ((ident list) option)
  | Return expression
  | EarlyReturn
  (* Break toLabel *)
  | Break (string option)
  (* TailRecurisve body *)
  | TailRecursive (statement list)
  | JumpTailCallStart
  | Halt
  | Print expression
End

Datatype:
  method =
  (* Method isStatic hasBody overridingPath name
            typeParams params body
            outTypes outVars *)
  | Method bool bool ((ident list) option) name
           (typeArgDecl list) (formal list) (statement list)
           (type list) ((ident list) option)
End

Datatype:
  field =
  (* Field formal defaultValue *)
  | Field formal (expression option)
End

Datatype:
  classItem =
  | ClassItem_Method(method)
End

Datatype:
  class =
  (* Class name enclosingModule typeParams superClasses fields
           body attributes *)
  | Class name ident (typeArgDecl list) (type list) (field list)
          (classItem list) (attribute list)
End

Datatype:
  trait =
  (* Trait name typeParams body attributes *)
  | Trait name (typeArgDecl list) (classItem list) (attribute list)
End

Datatype:
  newtype =
  (* Newtype name typeParams base range
             witnessStmts witnessExpr attributes *)
  | Newtype name (typeArgDecl list) type newtypeRange
            (statement list) (expression option) (attribute list)
End

Datatype:
  datatypeDtor =
  (* DatatypeDtor formal callName *)
  | DatatypeDtor formal (string option)
End

Datatype:
  datatypeCtor =
  (* DatatypeCtor name args hasAnyArgs (* includes ghost *) *)
  | DatatypeCtor name (datatypeDtor list) bool
End

Datatype:
  datatype =
  (* Datatype name enclosingModule typeParams ctors
              body isCo attributes *)
  | Datatype name ident (typeArgDecl list) (datatypeCtor list)
             (classItem list) bool (attribute list)
End

Datatype:
  module =
  (* Module name attributes body *)
  | Module name (attribute list) ((moduleItem list) option) ;

  moduleItem =
  | ModuleItem_Module module
  | ModuleItem_Class class
  | ModuleItem_Trait trait
  | ModuleItem_Newtype newtype
  | ModuleItem_Datatype datatype
End

val _ = export_theory();
