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
  | Primitive_Bool
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
  variance = Nonvariant | Covariant | Contravariant
End

Datatype:
  newtypeRange =
  (* bool determines whether arithmetic operations can overflow and wrap *)
  | U8 bool
  | I8 bool
  | U16 bool
  | I16 bool
  | U32 bool
  | I32 bool
  | U64 bool
  | I64 bool
  | U128 bool
  | I128 bool
  | NativeArrayIndex
  | BigInt
  | NewtypeRange_Bool
  | Sequence
  | NewtypeRange_Map
  | NoRange
End

Datatype:
  unaryOp = Not | BitwiseNot | Cardinality
End

Datatype:
  binOp =
  (* Eq referential *)
  | Eq bool
  (* Div overflow *)
  | Div bool | EuclidianDiv
  | Mod | EuclidianMod
  (* a ≤ b is !(b < a) *)
  | Lt | LtChar
  (* bool: overflow *)
  | Plus bool | Minus bool | Times bool
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
  traitType =
  (* Dafny: Traits that extend objects with --type-system-refresh,
     all traits otherwise *)
  | ObjectTrait
  (* Dafny: Traits that don't necessarily extend objects with
     --type-system-refresh *)
  | GeneralTrait
End

Datatype:
  typeParameterInfo =
  (* TypeParameterInfo variance necessaryForEqualitySupportOfSurroundingInductiveDatatype *)
  | TypeParameterInfo variance bool
End

Datatype:
  equalitySupport =
  | Never
  | ConsultTypeArguments
End

Datatype:
  resolvedTypeBase =
  | ResolvedTypeBase_Class
  (* ResolvedTypeBase_Datatype equalitySupport info *)
  | ResolvedTypeBase_Datatype equalitySupport (typeParameterInfo list)
  | ResolvedTypeBase_Trait traitType
  | ResolvedTypeBase_SynonymType type
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
  | Type_Map type type
  | SetBuilder type
  (* MapBuilder key value *)
  | MapBuilder type type
  (* Arrow args result *)
  | Arrow (type list) type
  | Primitive primitive | Passthrough string
  | TypeArg ident | Object
End

Datatype:
  typedBinOp =
  (* TypedBinOp op leftType rightType resultType *)
  | TypedBinOp binOp type type type
End

Datatype:
  typeArgBound =
  | SupportsEquality
  | SupportsDefault
  | TraitBound type
End

Datatype:
  typeArgDecl =
  (* TypeArgDecl name bounds info *)
  | TypeArgDecl ident (typeArgBound list) typeParameterInfo
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
  (* CallSignature parameters inheritedParams *)
  | CallSignature (formal list) (formal list)
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
  selectContext =
  | SelectContextDatatype
  | SelectContextGeneralTrait
  | SelectContextClassOrObjectTrait
End

(* Dafny comment:
   Since constant fields need to be set up in the constructor,
   accessing constant fields is done in two ways:
   - The internal field access (through the internal field that contains the
     value of the constant) it's not initialized at the beginning of the
     constructor.
   - The external field access (through a function), which when accessed
     must always be initialized.
   For Select expressions, it's important to know how the field is being
   accessed.
   For mutable fields, there is no wrapping function so only one way to access
   the mutable field *)
Datatype:
  fieldMutability =
  (* Access a class constant field after initialization, or a datatype constant
     field *)
  | ConstantField
  (* Access a class internal field before initialization, or a datatype
     destructor *)
  | InternalClassConstantFieldOrDatatypeDestructor
  | ClassMutableField
End

Datatype:
  assignLhs =
  | AssignLhs_Ident varName
  (* Select expr field isConstant *)
  | AssignLhs_Select expression varName bool
  (* Index expr indices *)
  | AssignLhs_Index expression (expression list) ;

  field =
  (* Field formal isConstant defaultValue isStatic *)
  | Field formal bool (expression option) bool ;

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
  (* MapValue mapElems domainType rangeType *)
  | MapValue ((expression # expression) list) type type
  (* MapBuilder keyType valueType *)
  | Expression_MapBuilder type type
  (* SeqUpdate expr indexExpr value collectionType exprType *)
  | SeqUpdate expression expression expression type type
  (* MapUpdate expr indexExpr value collectionType exprType *)
  | MapUpdate expression expression expression type type
  (* SetBuilder elemType *)
  | Expression_SetBuilder type
  | ToMultiset expression
  | This
  (* Ite cond thn els *)
  | Ite expression expression expression
  (* In contract to Dafny, we do not include formatting information *)
  | UnOp unaryOp expression type
  (* BinOp op left right *)
  | BinOp typedBinOp expression expression
  (* ArrayLen expr exprType dim native *)
  | ArrayLen expression type num bool
  | MapKeys expression
  | MapValues expression
  | MapItems expression
  (* Select expr field fieldMutability selectContext fieldType *)
  | Select expression varName fieldMutability selectContext type
  (* SelectFn expr field onDatatype isStatic isConstant arguments *)
  | SelectFn expression varName bool bool bool (type list)
  (* Index expr collKind indices *)
  | Index expression collKind (expression list)
  (* IndexRange expr isArray low high *)
  | IndexRange expression bool (expression option) (expression option)
  (* TupleSelect expr index dim fieldType *)
  | TupleSelect expression num num type
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
  | MultisetBoundedPool expression bool
  (* ExactBoundedPool of *)
  | ExactBoundedPool expression
  (* IntRange elemType lo hi up *)
  | IntRange type expression expression bool
  (* UnboundedIntRange start up *)
  | UnboundedIntRange expression bool
  (* Quantifier elemType collection is_forall lambda *)
  | Quantifier type expression bool expression ;

  statement =
  (* NOTE: We deviate from Dafny's definition of the IR to make
       compilation and semantics easier by adding ‘in’. *)
  (* DeclareVar name typ maybeValue in *)
  | DeclareVar varName type (expression option) (statement list)
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
  | Print expression type
  (* ConstructorNewSeparator fields *)
  | ConstructorNewSeparator (field list)
End

(* Dafny comment:
 * At this point, constraints have been entirely removed,
 * but synonym types might have different witnesses to use for by the compiler
 *)
Datatype:
  synonymType =
  (* SynonymType name typeParams base witnessStmts witnessExpr
                 attributes *)
  | SynonymType name (typeArgDecl list) type (statement list)
                (expression option) (attribute list)
End

Datatype:
  method =
  (* Method attributes isStatic hasBody outVarsAreUninitFieldsToAssign
            wasFunction overridingPath name typeParams params inheritedParams
            body outTypes outVars *)
  (* Comments from Dafny (probably Rust specific) *)
  (* outVarsAreUninitFieldsToAssign: for constructors *)
  (* wasFunction: to choose between "&self" and "&mut self" *)
  | Method (attribute list) bool bool bool bool ((ident list) option)
           name (typeArgDecl list) (formal list) (formal list) (statement list)
           (type list) ((varName list) option)
End

Datatype:
  classItem =
  | ClassItem_Method(method)
End

Datatype:
  trait =
  (* Trait name typeParams traitType parents downcastableTraits
           body attributes *)
  | Trait name (typeArgDecl list) traitType (type list) (type list)
          (classItem list) (attribute list)
End

Datatype:
  class =
  (* Class name enclosingModule typeParams superTraitTypes fields
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
             witnessStmts witnessExpr equalitySupport attributes classItems *)
  | Newtype name (typeArgDecl list) type newtypeRange
            (newtypeConstraint option) (statement list) (expression option)
            equalitySupport (attribute list) (classItem list)
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
              body isCo equalitySupport attributes superTraitTypes
              superTraitNegativeTypes *)
  (* superTraitNegativeTypes: Traits that one or more superTraits know they can
     downcast to, but the datatype does not.*)
  | Datatype name ident (typeArgDecl list) (datatypeCtor list)
             (classItem list) bool equalitySupport (attribute list) (type list)
             (type list)
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
                      wasFunction overridingPath nam typeParams params inheritedParams
                      body outTypes outVars) =
  (attributes, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction,
   overridingPath, nam, typeParams, params, inheritedParams, body, outTypes, outVars)
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
