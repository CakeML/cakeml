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
  varName =
  | VarName string
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
  | Native
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
  variance =
  | Nonvariant | Covariant | Contravariant
End

Datatype:
  typeArgDecl =
  (* TypeArgDecl name bounds variance *)
  | TypeArgDecl ident (typeArgBound list) variance
End

(* From Dafny:
 * USIZE is for whatever target considers that native arrays can be
 * indexed with *)
Datatype:
  newtypeRange =
  | U8 | I8
  | U16 | I16
  | U32 | I32
  | U64 | I64
  | U128 | I128
  | BigInt | USIZE
  | NoRange
End

Datatype:
  unaryOp =
  | Not | BitwiseNot
  | Cardinality
End

Datatype:
  binOp =
  (* Eq referential *)
  | Eq bool
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
  datatypeType = DatatypeType
End

Datatype:
  traitType = TraitType
End

Datatype:
  resolvedTypeBase =
  | ResolvedTypeBase_Class
  | ResolvedTypeBase_Datatype (variance list)
  | ResolvedTypeBase_Trait
  (* Newtype baseType range erase *)
  | ResolvedTypeBase_Newtype type newtypeRange bool ;

  resolvedType =
  (* ResolvedType path typeArgs kind attributes properMethods extendedTypes *)
  | ResolvedType (ident list) (type list) resolvedTypeBase (attribute list)
                 (name list) (type list) ;

  type =
  | UserDefined resolvedType
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
  | TypeArg ident | Object
End

Datatype:
  newtypeType =
  (* NewtypeType baseType range erase *)
  | NewtypeType type newtypeRange bool
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
  | Formal varName type (attribute list)
End

Datatype:
  callSignature =
  (* CallSignature parameters *)
  | CallSignature (formal list)
End

Datatype:
  callName =
  (* CallName name onType receiverArg receiverAsArgument signature *)
  | CallName name (type option) (formal option) bool callSignature
  | MapBuilderAdd
  | MapBuilderBuild
  | SetBuilderAdd
  | SetBuilderBuild
End

Datatype:
  assignLhs =
  | AssignLhs_Ident varName
  (* Select expr field *)
  | AssignLhs_Select expression varName
  (* Index expr indices *)
  | AssignLhs_Index expression (expression list) ;

  expression =
  | Literal literal
  | Expression_Ident varName
  (* Companion ids typeArgs *)
  | Companion (ident list) (type list)
  | ExternCompanion (ident list)
  | Expression_Tuple (expression list)
  (* New path typeArgs args *)
  | New (ident list) (type list) (expression list)
  (* NewUninitArray dims typ *)
  | NewUninitArray (expression list) type
  | ArrayIndexToInt expression
  | FinalizeNewArray expression type
  (* DatatypeValue datatypeType typeArgs variant isCo contents *)
  | DatatypeValue resolvedType (type list) name bool
                  ((varName # expression) list)
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
  (* ArrayLen expr exprType dim native *)
  | ArrayLen expression type num bool
  | MapKeys expression
  | MapValues expression
  | MapItems expression
  (* Select expr field isConstant onDatatype fieldType *)
  | Select expression varName bool bool type
  (* SelectFn expr field onDatatype isStatic isConstant arguments *)
  | SelectFn expression varName bool bool bool (type list)
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
  | IIFE varName type expression expression
  (* Apply expr args *)
  | Apply expression (expression list)
  (* TypeTest on dType variant *)
  | TypeTest expression (ident list) name
  (* Is expr fromType toType *)
  | Is expression type type
  | InitializationValue type
  | BoolBoundedPool
  (* SetBoundedPool of *)
  | SetBoundedPool expression
  (* MapBoundedPool of *)
  | MapBoundedPool expression
  (* SeqBoundedPool of includeDuplicates *)
  | SeqBoundedPool expression bool
  (* ExactBoundedPool of *)
  | ExactBoundedPool expression
  (* IntRange elemType lo hi up *)
  | IntRange type expression expression bool
  (* UnboundedIntRange start up *)
  | UnboundedIntRange expression bool
  (* Quantifier elemType collection is_forall lambda *)
  | Quantifier type expression bool expression ;

  statement =
  | DeclareVar varName type (expression option)
  | Assign assignLhs expression
  (* If cond thn els *)
  | If expression (statement list) (statement list)
  (* Labeled lbl body *)
  | Labeled string (statement list)
  | While expression (statement list)
  (* Foreach boundName boundType over body *)
  | Foreach varName type expression (statement list)
  (* Call on callName typeArgs args outs *)
  | Call expression callName (type list) (expression list)
         ((varName list) option)
  | Return expression
  | EarlyReturn
  (* Break toLabel *)
  | Break (string option)
  (* TailRecurisve body *)
  | TailRecursive (statement list)
  | JumpTailCallStart
  | Halt
  | Print expression
  (* ConstructorNewSeparator fields *)
  | ConstructorNewSeparator (formal list)
End

(* Dafny comment:
 * At this point, constraints have been entirely removed,
 * but synonym types might have different witnesses to use for by the compiler
 *)
Datatype:
  synonymType =
  | SynonymType name (typeArgDecl list) type (statement list)
                (expression option) (attribute list)
End

Datatype:
  method =
  (* Method attributes isStatic hasBody outVarsAreUninitFieldsToAssign
            wasFunction overridingPath name typeParams params body outTypes
            outVars *)
  (* Comments from Dafny (probably Rust specific) *)
  (* outVarsAreUninitFieldsToAssign: for constructors *)
  (* wasFunction: to choose between "&self" and "&mut self" *)
  | Method (attribute list) bool bool bool bool ((ident list) option) name
           (typeArgDecl list) (formal list) (statement list)
           (type list) ((varName list) option)
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
  trait =
  (* Trait name typeParams parents body attributes *)
  | Trait name (typeArgDecl list) (type list) (classItem list) (attribute list)
End

Datatype:
  class =
  (* Class name enclosingModule typeParams superClasses fields
           body attributes *)
  | Class name ident (typeArgDecl list) (type list) (field list)
          (classItem list) (attribute list)
End

Datatype:
  newtypeConstraint =
  (* NewtypeConstraint variable constraintStmts *)
  | NewtypeConstraint formal (statement list)
End

Datatype:
  newtype =
  (* Newtype name typeParams base range constraint
             witnessStmts witnessExpr attributes *)
  | Newtype name (typeArgDecl list) type newtypeRange (newtypeConstraint option)
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
  (* Module name attributes requiresExterns body *)
  | Module name (attribute list) bool ((moduleItem list) option) ;

  moduleItem =
  | ModuleItem_Module module
  | ModuleItem_Class class
  | ModuleItem_Trait trait
  | ModuleItem_Newtype newtype
  | ModuleItem_SynonymType synonymType
  | ModuleItem_Datatype datatype
End

Definition dest_Ident_def:
  dest_Ident (Ident n) = n
End

Definition dest_varName_def:
  dest_varName (VarName s) = s
End

Definition dest_Method_def:
  dest_Method (Method attributes isStatic hasBody outVarsAreUninitFieldsToAssign
                      wasFunction overridingPath nam typeParams params body
                      outTypes outVars) =
  (attributes, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction,
   overridingPath, nam, typeParams, params, body, outTypes, outVars)
End

(* Adapted from
 * https://github.com/dafny-lang/dafny/blob/bc6b587e264e3c531c4d6698abd421abdff3aea9/Source/DafnyCore/Generic/Util.cs#L341
 *)
Definition unescape_string_def:
  (unescape_string (c1::c2::rest) verbatim =
  if verbatim then
    if c1 = #"\"" ∧ c2 = #"\"" then
      #"\""::(unescape_string rest verbatim)
    else
      c1::(unescape_string (c2::rest) verbatim)
  else if c1 = #"\\" ∧ c2 = #"'" then
    #"'"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\"" then
    #"\""::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\\" then
    #"\\"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"0" then
    #"\000"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"n" then
    #"\n"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"r" then
    #"\r"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"t" then
    #"\t"::(unescape_string rest verbatim)
  else
    c1::(unescape_string (c2::rest) verbatim)) ∧
  (unescape_string (c::rest) verbatim = c::(unescape_string rest verbatim)) ∧
  (unescape_string "" _ = "")
End

val _ = export_theory();
