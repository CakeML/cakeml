(*
  Definition of functions to generate Dafny's abstract syntax tree.
*)

open preamble
open dafny_sexpTheory
open dafny_astTheory
open basicSizeTheory

val _ = new_theory "sexp_to_dafny";

val _ = enable_monadsyntax ();
val _ = enable_monad "option";

(*
 * Helpers
 *)

(* TODO Swap to monad defined in dafny_util *)
(* TODO rename sexp_to_dafnyScript *)
(* TODO rename str to s *)
(* TODO update stale names referring to old sexp type *)

Definition dstrip_sexp_def:
  dstrip_sexp (Expr ((Atom s)::rest)) = return (s, rest) ∧
  dstrip_sexp _ = fail
End

Definition strip_sxcons_def:
  strip_sxcons (Expr ses) = return ses ∧
  strip_sxcons _ = fail
End

(* sexp -> (string option) *)
Definition sxstr_to_str_def:
  (sxstr_to_str (Atom str) = return str) ∧
  (sxstr_to_str _ = fail)
End

(* As described above, this function is probably wrong due to the way
   Dafny deals with characters. *)
(* sexp -> (char option) *)
Definition sxstr_to_ch_def:
  (sxstr_to_ch (Atom [c]) = return c) ∧
  (sxstr_to_ch _ = fail)
End

(* sexp -> (num option) *)
Definition sxnum_to_num_def:
  (sxnum_to_num (Atom s) = fromNatString (implode s)) ∧
  (sxnum_to_num _ = fail)
End

(* sexp -> (bool option) *)
Definition sxsym_to_bool_def:
  (sxsym_to_bool (Atom str) =
   (* We do not use case on strings, since the resulting theorem blows up for
      some reason *)
   if (str = "true") then
     return T
   else if (str = "false") then
     return F
   else fail) ∧
  (sxsym_to_bool _ = fail)
End

(* sexp -> ((sexp option) option) *)
(* The outer option indicates whether the conversion to the inner option was
   successful. *)
Definition sxsym_to_opt_def:
  sxsym_to_opt se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "None" ∧ LENGTH args = 0) then
      return NONE
    else if (ss = "Some" ∧ LENGTH args = 1) then
      return (SOME (EL 0 args))
    else fail
  od
End
(* TODO: test this *)

(* If possible, interprets the S-expression as a list and maps the given
   function over it. *)
(* (sexp -> (α option)) -> sexp -> ((α list) option) *)
Definition opt_mmap_sexp_list_def:
  opt_mmap_sexp_list f ses =
  do
    ses <- strip_sxcons ses;
    OPT_MMAP f ses
  od
End

(* If possible, interprets the S-expression as a tuple and maps the functions
   accordingly. *)
(* (sexp -> (α option)) -> (sexp -> (β option)) -> sexp -> ((α # β) option) *)
Definition opt_mmap_sexp_tuple_def:
  opt_mmap_sexp_tuple f1 f2 ses =
  do
    ses <- strip_sxcons ses;
    assert (LENGTH ses = 2);
    t1 <- f1 (EL 0 ses);
    t2 <- f2 (EL 1 ses);
    return (t1, t2)
  od
End

(* If possible, interprets the S-expression as a list of tuples and maps the
   functions accordingly. *)
(* (sexp -> (α option)) -> (sexp -> (β option)) -> sexp -> (((α # β) list) option) *)
Definition opt_mmap_sexp_tuple_list_def:
  opt_mmap_sexp_tuple_list f1 f2 ses =
  opt_mmap_sexp_list (λ t. opt_mmap_sexp_tuple f1 f2 t) ses
End
(* TODO: test this *)

(*
 * Converting S-expressions to Dafny's AST
 *)

(* sexp -> (ident option) *)
Definition sexp_name_def:
  sexp_name se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Name.Name" ∧ LENGTH args = 1);
    str <- sxstr_to_str (EL 0 args);
    return (Name str)
  od
End

(* sexp -> (ident option) *)
Definition sexp_ident_def:
  sexp_ident se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Ident.Ident" ∧ LENGTH args = 1);
    n <- sexp_name (EL 0 args);
    return (Ident n)
  od
End

(* sexp -> (attribute option) *)
Definition sexp_attribute_def:
  sexp_attribute se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Attribute.Attribute" ∧ LENGTH args = 2);
    nam <- sxstr_to_str (EL 0 args);
    attr_args <- opt_mmap_sexp_list sxstr_to_str (EL 1 args);
    return (Attribute nam attr_args)
  od
End

(* sexp -> (primitive option) *)
Definition sexp_primitive_def:
  sexp_primitive se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "Primitive.Int") then
      return Int
    else if (ss = "Primitive.Real") then
      return Real
    else if (ss = "Primitive.String") then
      return String
    else if (ss = "Primitive.Bool") then
      return Bool
    else if (ss = "Primitive.Char") then
      return Char
    else fail
  od
End

(* sexp -> (collKind option) *)
Definition sexp_collKind_def:
  sexp_collKind se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "CollKind.Seq") then
      return CollKind_Seq
    else if (ss = "CollKind.Array") then
      return CollKind_Array
    else if (ss = "CollKind.Map") then
      return CollKind_Map
    else fail
  od
End

(* sexp -> (typeArgBound option) *)
Definition sexp_typeArgBound_def:
  sexp_typeArgBound se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "TypeArgBound.SupportsEquality") then
      return SupportsEquality
    else if (ss = "TypeArgBound.SupportsDefault") then
      return SupportsDefault
    else fail
  od
End
(* TODO Missing test *)

(* sexp -> (typeArgDecl option) *)
Definition sexp_typeArgDecl_def:
  sexp_typeArgDecl se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "TypeArgDecl.TypeArgDecl" ∧ LENGTH args = 2);
    nam <- sexp_ident (EL 0 args);
    bounds <- opt_mmap_sexp_list sexp_typeArgBound (EL 1 args);
    return (TypeArgDecl nam bounds)
  od
End

(* sexp -> (newtypeRange option) *)
Definition sexp_newtypeRange_def:
  sexp_newtypeRange se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "NewtypeRange.U8") then
      return U8
    else if (ss = "NewtypeRange.I8") then
      return I8
    else if (ss = "NewtypeRange.U16") then
      return U16
    else if (ss = "NewtypeRange.I16") then
      return I16
    else if (ss = "NewtypeRange.U32") then
      return U32
    else if (ss = "NewtypeRange.I32") then
      return I32
    else if (ss = "NewtypeRange.U64") then
      return U64
    else if (ss = "NewtypeRange.I64") then
      return I64
    else if (ss = "NewtypeRange.U128") then
      return U128
    else if (ss = "NewtypeRange.I128") then
      return I128
    else if (ss = "NewtypeRange.BigInt") then
      return BigInt
    else if (ss = "NewtypeRange.NoRange") then
      return NoRange
    else fail
  od
End

(* sexp -> (unaryOp option) *)
Definition sexp_unaryOp_def:
  sexp_unaryOp se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "UnaryOp.Not") then
      return Not
    else if (ss = "UnaryOp.BitwiseNot") then
      return BitwiseNot
    else if (ss = "UnaryOp.Cardinality") then
      return Cardinality
    else fail
  od
End

(* sexp -> (binOp option) *)
Definition sexp_binOp_def:
  sexp_binOp se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "BinOp.Eq" ∧ LENGTH args = 2) then
      do
        referential <- sxsym_to_bool (EL 0 args);
        nullable <- sxsym_to_bool (EL 1 args);
        return (Eq referential nullable)
      od
    else if (ss = "BinOp.Div" ∧ LENGTH args = 0) then
      return Div
    else if (ss = "BinOp.EuclidianDiv" ∧ LENGTH args = 0) then
      return EuclidianDiv
    else if (ss = "BinOp.Mod" ∧ LENGTH args = 0) then
      return Mod
    else if (ss = "BinOp.EuclidianMod" ∧ LENGTH args = 0) then
      return EuclidianMod
    else if (ss = "BinOp.Lt" ∧ LENGTH args = 0) then
      return Lt
    else if (ss = "BinOp.LtChar" ∧ LENGTH args = 0) then
      return LtChar
    else if (ss = "BinOp.Plus" ∧ LENGTH args = 0) then
      return Plus
    else if (ss = "BinOp.Minus" ∧ LENGTH args = 0) then
      return Minus
    else if (ss = "BinOp.Times" ∧ LENGTH args = 0) then
      return Times
    else if (ss = "BinOp.BitwiseAnd" ∧ LENGTH args = 0) then
      return BitwiseAnd
    else if (ss = "BinOp.BitwiseOr" ∧ LENGTH args = 0) then
      return BitwiseOr
    else if (ss = "BinOp.BitwiseXor" ∧ LENGTH args = 0) then
      return BitwiseXor
    else if (ss = "BinOp.BitwiseShiftRight" ∧ LENGTH args = 0) then
      return BitwiseShiftRight
    else if (ss = "BinOp.BitwiseShiftLeft" ∧ LENGTH args = 0) then
      return BitwiseShiftLeft
    else if (ss = "BinOp.And" ∧ LENGTH args = 0) then
      return And
    else if (ss = "BinOp.Or" ∧ LENGTH args = 0) then
      return Or
    else if (ss = "BinOp.In" ∧ LENGTH args = 0) then
      return In
    else if (ss = "BinOp.SeqProperPrefix" ∧ LENGTH args = 0) then
      return SeqProperPrefix
    else if (ss = "BinOp.SeqPrefix" ∧ LENGTH args = 0) then
      return SeqPrefix
    else if (ss = "BinOp.SetMerge" ∧ LENGTH args = 0) then
      return SetMerge
    else if (ss = "BinOp.SetSubtraction" ∧ LENGTH args = 0) then
      return SetSubtraction
    else if (ss = "BinOp.SetIntersection" ∧ LENGTH args = 0) then
      return SetIntersection
    else if (ss = "BinOp.Subset" ∧ LENGTH args = 0) then
      return Subset
    else if (ss = "BinOp.ProperSubset" ∧ LENGTH args = 0) then
      return ProperSubset
    else if (ss = "BinOp.SetDisjoint" ∧ LENGTH args = 0) then
      return SetDisjoint
    else if (ss = "BinOp.MapMerge" ∧ LENGTH args = 0) then
      return MapMerge
    else if (ss = "BinOp.MapSubtraction" ∧ LENGTH args = 0) then
      return MapSubtraction
    else if (ss = "BinOp.MultisetMerge" ∧ LENGTH args = 0) then
      return MultisetMerge
    else if (ss = "BinOp.MultisetSubtraction" ∧ LENGTH args = 0) then
      return MultisetSubtraction
    else if (ss = "BinOp.MultisetIntersection" ∧ LENGTH args = 0) then
      return MultisetIntersection
    else if (ss = "BinOp.Submultiset" ∧ LENGTH args = 0) then
      return Submultiset
    else if (ss = "BinOp.ProperSubmultiset" ∧ LENGTH args = 0) then
      return ProperSubmultiset
    else if (ss = "BinOp.MultisetDisjoint" ∧ LENGTH args = 0) then
      return MultisetDisjoint
    else if (ss = "BinOp.Concat" ∧ LENGTH args = 0) then
      return Concat
    else if (ss = "BinOp.Passthrough" ∧ LENGTH args = 1) then
    do
      str <- sxstr_to_str (EL 0 args);
      return (BinOp_Passthrough str)
    od
    else fail
  od
End

(* sexp -> (datatypeType option) *)
Definition sexp_datatypeType_def:
  sexp_datatypeType se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "DatatypeType.DatatypeType" ∧ LENGTH args = 2);
    path <- opt_mmap_sexp_list sexp_ident (EL 0 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 1 args);
    return (DatatypeType path attrs)
  od
End
(* TODO add test *)

(* Defines the mutually recursive functions
 * sexp_resolvedType: sexp -> (resolvedType option)
 * sexp_type: sexp -> (type option) *)
Definition sexp_type_def:
  (sexp_type se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "Type.Path" ∧ LENGTH args = 3) then
       do
         ids <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         typeArgs <- map_sexp_type arg1_list;
         resolved <- sexp_resolvedType (EL 2 args);
         return (Path ids typeArgs resolved)
       od
     else if (ss = "Type.Nullable" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (Nullable typ)
       od
     else if (ss = "Type.Tuple" ∧ LENGTH args = 1) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         typs <- map_sexp_type arg0_list;
         return (Tuple typs)
       od
     else if (ss = "Type.Array" ∧ LENGTH args = 2) then
       do
         element <- sexp_type (EL 0 args);
         dims <- sxnum_to_num (EL 1 args);
         return (Array element dims)
       od
     else if (ss = "Type.Seq" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (Seq typ)
       od
     else if (ss = "Type.Set" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (Set typ)
       od
     else if (ss = "Type.Multiset" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (Multiset typ)
       od
     else if (ss = "Type.Map" ∧ LENGTH args = 2) then
       do
         key <- sexp_type (EL 0 args);
         value <- sexp_type (EL 1 args);
         return (Map key value)
       od
     else if (ss = "Type.SetBuilder" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (SetBuilder typ)
       od
     else if (ss = "Type.MapBuilder" ∧ LENGTH args = 2) then
       do
         key <- sexp_type (EL 0 args);
         value <- sexp_type (EL 1 args);
         return (MapBuilder key value)
       od
     else if (ss = "Type.Arrow" ∧ LENGTH args = 2) then
       do
         (* shadowing args is not a good idea *)
         arg0_list <- strip_sxcons (EL 0 args);
         arr_args <- map_sexp_type arg0_list;
         result <- sexp_type (EL 1 args);
         return (Arrow arr_args result)
       od
     else if (ss = "Type.Primitive" ∧ LENGTH args = 1) then
       do
         prim <- sexp_primitive (EL 0 args);
         return (Primitive prim)
       od
     else if (ss = "Type.Passthrough" ∧ LENGTH args = 1) then
       do
         str <- sxstr_to_str (EL 0 args);
         return (Passthrough str)
       od
     else if (ss = "Type.TypeArg" ∧ LENGTH args = 1) then
       do
         id <- sexp_ident (EL 0 args);
         return (TypeArg id)
       od
     else fail
   od)
  ∧
  (map_sexp_type ses =
   case ses of
   | [] => return []
   | (se::rest) =>
       do
         fse <- sexp_type se;
         frest <- map_sexp_type rest;
         return (fse::frest)
       od) ∧
  (sexp_resolvedType se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "ResolvedType.Datatype" ∧ LENGTH args = 1) then
       do
         dt <- sexp_datatypeType (EL 0 args);
         return (ResolvedType_Datatype dt)
       od
     else if (ss = "ResolvedType.Trait" ∧ LENGTH args = 2) then
       do
         path <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         attrs <- opt_mmap_sexp_list sexp_attribute (EL 1 args);
         return (ResolvedType_Trait path attrs)
       od
     else if (ss = "ResolvedType.Newtype" ∧ LENGTH args = 4) then
       do
         baseType <- sexp_type (EL 0 args);
         range <- sexp_newtypeRange (EL 1 args);
         erase <- sxsym_to_bool (EL 2 args);
         attrs <- opt_mmap_sexp_list sexp_attribute (EL 3 args);
         return (ResolvedType_Newtype baseType range erase attrs)
       od
     else fail
   od)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL se => sexp_size se
                            | INR (INL ses) => list_size sexp_size ses
                            | INR (INR se) => sexp_size se’ \\ rw[]
  \\ gvs[LENGTH_EQ_NUM_compute, oneline dstrip_sexp_def, sexp_size_def,
         AllCaseEqs(), oneline strip_sxcons_def, sexp_size_eq]
End

(* sexp -> (literal option) *)
Definition sexp_literal_def:
  sexp_literal se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "Literal.BoolLiteral" ∧ LENGTH args = 1) then
      do
        b <- sxsym_to_bool (EL 0 args);
        return (BoolLiteral b)
      od
    else if (ss = "Literal.IntLiteral" ∧ LENGTH args = 2) then
      do
        str <- sxstr_to_str (EL 0 args);
        t <- sexp_type (EL 1 args);
        return (IntLiteral str t)
      od
    else if (ss = "Literal.DecLiteral" ∧ LENGTH args = 3) then
      do
        str1 <- sxstr_to_str (EL 0 args);
        str2 <- sxstr_to_str (EL 1 args);
        t <- sexp_type (EL 2 args);
        return (DecLiteral str1 str2 t)
      od
    else if (ss = "Literal.StringLiteral" ∧ LENGTH args = 2) then
      do
        str <- sxstr_to_str (EL 0 args);
        verbatim <- sxsym_to_bool (EL 1 args);
        return (StringLiteral str verbatim)
      od
    else if (ss = "Literal.CharLiteral" ∧ LENGTH args = 1) then
      do
        ch <- sxstr_to_ch (EL 0 args);
        return (CharLiteral ch)
      od
    else if (ss = "Literal.CharLiteralUTF16" ∧ LENGTH args = 1) then
      do
        n <- sxnum_to_num (EL 0 args);
        return (CharLiteralUTF16 n)
      od
    else if (ss = "Literal.Null" ∧ LENGTH args = 1) then
      do
        typ <- sexp_type (EL 0 args);
        return (Null typ)
      od
    else fail
  od
End

(* sexp -> (formal option) *)
Definition sexp_formal_def:
  sexp_formal se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Formal.Formal" ∧ LENGTH args = 3);
    n <- sexp_name (EL 0 args);
    typ <- sexp_type (EL 1 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 2 args);
    return (Formal n typ attrs)
  od
End

(* sexp -> (callSignature option) *)
Definition sexp_callSignature_def:
  sexp_callSignature se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "CallSignature.CallSignature" ∧ LENGTH args = 1);
    params <- opt_mmap_sexp_list sexp_formal (EL 0 args);
    return (CallSignature params)
  od
End

(* sexp -> (callName option) *)
Definition sexp_callName_def:
  sexp_callName se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "CallName.CallName" ∧ LENGTH args = 3) then
      do
        n <- sexp_name (EL 0 args);
        (* TODO turn rhs into option/error
           return_option (sysym_to_opt ..), define using return/fail *)
        opt <- sxsym_to_opt (EL 1 args);
        typ_opt <<- monad_bind opt sexp_type;
        sig <- sexp_callSignature (EL 2 args);
        return (CallName n typ_opt sig)
      od
    else if (ss = "CallName.MapBuilderAdd" ∧ LENGTH args = 0) then
      return MapBuilderAdd
    else if (ss = "CallName.MapBuilderBuild" ∧ LENGTH args = 0) then
      return MapBuilderBuild
    else if (ss = "CallName.SetBuilderAdd" ∧ LENGTH args = 0) then
      return SetBuilderAdd
    else if (ss = "CallName.SetBuilderBuild" ∧ LENGTH args = 0) then
      return SetBuilderBuild
    else fail
  od
End

(* Defines the mutually recursive functions
   sexp_assignLhs: sexp -> (assignLhs option)
   sexp_expression: sexp -> (expression option)
   sexp_statement: sexp -> (statement option) *)
Definition sexp_statement_def:
  (sexp_assignLhs se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "AssignLhs.Ident" ∧ LENGTH args = 1) then
       do
         id <- sexp_ident (EL 0 args);
         return (AssignLhs_Ident id)
       od
     else if (ss = "AssignLhs.Select" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_name (EL 1 args);
         return (AssignLhs_Select expr field)
       od
     else if (ss = "AssignLhs.Index" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         indices <- opt_mmap_sexp_list sexp_expression (EL 1 args);
         return (AssignLhs_Index expr indices)
       od
     else fail
   od)
  ∧
  (sexp_expression se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "Expression.Literal" ∧ LENGTH args = 1) then
       do
         lit <- sexp_literal (EL 0 args);
         return (Literal lit)
       od
     else if (ss = "Expression.Ident" ∧ LENGTH args = 1) then
       do
         n <- sexp_name (EL 0 args);
         return (Expression_Ident n)
       od
     else if (ss = "Expression.Companion" ∧ LENGTH args = 1) then
       do
         ids <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         return (Companion ids)
       od
     else if (ss = "Expression.Tuple" ∧ LENGTH args = 1) then
       do
         exprs <- opt_mmap_sexp_list sexp_expression (EL 0 args);
         return (Expression_Tuple exprs)
       od
     else if (ss = "Expression.New" ∧ LENGTH args = 3) then
       do
         path <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 1 args);
         new_args <- opt_mmap_sexp_list sexp_expression (EL 2 args);
         return (New path typeArgs new_args)
       od
     else if (ss = "Expression.NewArray" ∧ LENGTH args = 2) then
       do
         dims <- opt_mmap_sexp_list sexp_expression (EL 0 args);
         typ <- sexp_type (EL 1 args);
         return (NewArray dims typ)
       od
     else if (ss = "Expression.DatatypeValue" ∧ LENGTH args = 5) then
       do
         dtType <- sexp_datatypeType (EL 0 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 1 args);
         variant <- sexp_name (EL 2 args);
         isCo <- sxsym_to_bool (EL 3 args);
         contents <- opt_mmap_sexp_tuple_list sxstr_to_str
                                              sexp_expression
                                              (EL 4 args);
         return (DatatypeValue dtType typeArgs variant isCo contents)
       od
     else if (ss = "Expression.Convert" ∧ LENGTH args = 3) then
       do
         v <- sexp_expression (EL 0 args);
         from <- sexp_type (EL 1 args);
         typ <- sexp_type (EL 2 args);
         return (Convert v from typ)
       od
     else if (ss = "Expression.SeqConstruct" ∧ LENGTH args = 2) then
       do
         len <- sexp_expression (EL 0 args);
         elem <- sexp_expression (EL 1 args);
         return (SeqConstruct len elem)
       od
     else if (ss = "Expression.SeqValue" ∧ LENGTH args = 2) then
       do
         exprs <- opt_mmap_sexp_list sexp_expression (EL 0 args);
         typ <- sexp_type (EL 1 args);
         return (SeqValue exprs typ)
       od
     else if (ss = "Expression.SetValue" ∧ LENGTH args = 1) then
       do
         exprs <- opt_mmap_sexp_list sexp_expression (EL 0 args);
         return (SetValue exprs)
       od
     else if (ss = "Expression.MultisetValue" ∧ LENGTH args = 1) then
       do
         exprs <- opt_mmap_sexp_list sexp_expression (EL 0 args);
         return (MultisetValue exprs)
       od
     else if (ss = "Expression.MapValue" ∧ LENGTH args = 1) then
       do
         e_tuples <- opt_mmap_sexp_tuple_list sexp_expression
                                              sexp_expression
                                              (EL 0 args);
         return (MapValue e_tuples)
       od
     else if (ss = "Expression.MapBuilder" ∧ LENGTH args = 2) then
       do
         keyTyp <- sexp_type (EL 0 args);
         valTyp <- sexp_type (EL 1 args);
         return (Expression_MapBuilder keyTyp valTyp)
       od
     else if (ss = "Expression.SeqUpdate" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         indexExpr <- sexp_expression (EL 1 args);
         v <- sexp_expression (EL 2 args);
         return (SeqUpdate expr indexExpr v)
       od
     else if (ss = "Expression.MapUpdate" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         indexExpr <- sexp_expression (EL 1 args);
         v <- sexp_expression (EL 2 args);
         return (MapUpdate expr indexExpr v)
       od
     else if (ss = "Expression.SetBuilder" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (Expression_SetBuilder typ)
       od
     else if (ss = "Expression.ToMultiset" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (ToMultiset expr)
       od
     else if (ss = "Expression.This" ∧ LENGTH args = 0) then
       return This
     else if (ss = "Expression.Ite" ∧ LENGTH args = 3) then
       do
         cond <- sexp_expression (EL 0 args);
         thn <- sexp_expression (EL 1 args);
         els <- sexp_expression (EL 2 args);
         return (Ite cond thn els)
       od
     else if (ss = "Expression.UnOp" ∧ LENGTH args = 2) then
       do
         uOp <- sexp_unaryOp (EL 0 args);
         expr <- sexp_expression (EL 1 args);
         return (UnOp uOp expr)
       od
     else if (ss = "Expression.BinOp" ∧ LENGTH args = 3) then
       do
         op <- sexp_binOp (EL 0 args);
         left <- sexp_expression (EL 1 args);
         right <- sexp_expression (EL 2 args);
         return (BinOp op left right)
       od
     else if (ss = "Expression.ArrayLen" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         dim <- sxnum_to_num (EL 1 args);
         return (ArrayLen expr dim)
       od
     else if (ss = "Expression.MapKeys" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (MapKeys expr)
       od
     else if (ss = "Expression.MapValues" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (MapValues expr)
       od
     else if (ss = "Expression.Select" ∧ LENGTH args = 5) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_name (EL 1 args);
         isConstant <- sxsym_to_bool (EL 2 args);
         onDatatype <- sxsym_to_bool (EL 3 args);
         fieldTyp <- sexp_type (EL 4 args);
         return (Select expr field isConstant onDatatype fieldTyp)
       od
     else if (ss = "Expression.SelectFn" ∧ LENGTH args = 5) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_name (EL 1 args);
         onDatatype <- sxsym_to_bool (EL 2 args);
         isStatic <- sxsym_to_bool (EL 3 args);
         arity <- sxnum_to_num (EL 4 args);
         return (SelectFn expr field onDatatype isStatic arity)
       od
     else if (ss = "Expression.Index" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         cK <- sexp_collKind (EL 1 args);
         indices <- opt_mmap_sexp_list sexp_expression (EL 2 args);
         return (Index expr cK indices)
       od
     else if (ss = "Expression.IndexRange" ∧ LENGTH args = 4) then
       do
         expr <- sexp_expression (EL 0 args);
         isArray <- sxsym_to_bool (EL 1 args);
         opt <- sxsym_to_opt (EL 2 args);
         low <<- monad_bind opt sexp_expression;
         opt <- sxsym_to_opt (EL 3 args);
         high <<- monad_bind opt sexp_expression;
         return (IndexRange expr isArray low high)
       od
     else if (ss = "Expression.TupleSelect" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         index <- sxnum_to_num (EL 1 args);
         fieldTyp <- sexp_type (EL 2 args);
         return (TupleSelect expr index fieldTyp)
       od
     else if (ss = "Expression.Call" ∧ LENGTH args = 4) then
       do
         on <- sexp_expression (EL 0 args);
         callName <- sexp_callName (EL 1 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 2 args);
         call_args <- opt_mmap_sexp_list sexp_expression (EL 3 args);
         return (Expression_Call on callName typeArgs call_args)
       od
     else if (ss = "Expression.Lambda" ∧ LENGTH args = 3) then
       do
         params <- opt_mmap_sexp_list sexp_formal (EL 0 args);
         retTyp <- sexp_type (EL 1 args);
         body <- opt_mmap_sexp_list sexp_statement (EL 2 args);
         return (Lambda params retTyp body)
       od
     else if (ss = "Expression.BetaRedex" ∧ LENGTH args = 3) then
       do
         vs <- opt_mmap_sexp_tuple_list sexp_formal
                                        sexp_expression
                                        (EL 0 args);
         retTyp <- sexp_type (EL 1 args);
         expr <- sexp_expression (EL 2 args);
         return (BetaRedex vs retTyp expr)
       od
     else if (ss = "Expression.IIFE" ∧ LENGTH args = 4) then
       do
         name <- sexp_ident (EL 0 args);
         typ <- sexp_type (EL 1 args);
         v <- sexp_expression (EL 2 args);
         iifeBody <- sexp_expression (EL 3 args);
         return (IIFE name typ v iifeBody)
       od
     else if (ss = "Expression.Apply" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         app_args <- opt_mmap_sexp_list sexp_expression (EL 1 args);
         return (Apply expr app_args)
       od
     else if (ss = "Expression.TypeTest" ∧ LENGTH args = 3) then
       do
         on <- sexp_expression (EL 0 args);
         dType <- opt_mmap_sexp_list sexp_ident (EL 1 args);
         vrnt <- sexp_name (EL 2 args);
         return (TypeTest on dType vrnt)
       od
     else if (ss = "Expression.InitializationValue" ∧ LENGTH args = 1) then
       do
         typ <- sexp_type (EL 0 args);
         return (InitializationValue typ)
       od
     else if (ss = "Expression.BoolBoundedPool" ∧ LENGTH args = 0) then
       return BoolBoundedPool
     else if (ss = "Expression.SetBoundedPool" ∧ LENGTH args = 1) then
       do
         of_expr <- sexp_expression (EL 0 args);
         return (SetBoundedPool of_expr)
       od
     else if (ss = "Expression.SeqBoundedPool" ∧ LENGTH args = 2) then
       do
         of_expr <- sexp_expression (EL 0 args);
         includeDuplicates <- sxsym_to_bool (EL 1 args);
         return (SeqBoundedPool of_expr includeDuplicates)
       od
     else if (ss = "Expression.IntRange" ∧ LENGTH args = 2) then
       do
         lo <- sexp_expression (EL 0 args);
         hi <- sexp_expression (EL 1 args);
         return (IntRange lo hi)
       od
     else fail
   od
  )
  ∧
  (sexp_statement se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "Statement.DeclareVar" ∧ LENGTH args = 3) then
       do
         n <- sexp_name (EL 0 args);
         typ <- sexp_type (EL 1 args);
         (* TODO Extract this pattern opt <- ... out? *)
         opt <- sxsym_to_opt (EL 2 args);
         expr <<- monad_bind opt sexp_expression;
         return (DeclareVar n typ expr)
       od
     else if (ss = "Statement.Assign" ∧ LENGTH args = 2) then
       do
         assLhs <- sexp_assignLhs (EL 0 args);
         expr <- sexp_expression (EL 1 args);
         return (Assign assLhs expr)
       od
     else if (ss = "Statement.If" ∧ LENGTH args = 3) then
       do
         cond <- sexp_expression (EL 0 args);
         thn <- opt_mmap_sexp_list sexp_statement (EL 1 args);
         els <- opt_mmap_sexp_list sexp_statement (EL 2 args);
         return (If cond thn els)
       od
     else if (ss = "Statement.Labeled" ∧ LENGTH args = 2) then
       do
         lbl <- sxstr_to_str (EL 0 args);
         body <- opt_mmap_sexp_list sexp_statement (EL 1 args);
         return (Labeled lbl body)
       od
     else if (ss = "Statement.While" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         stmts <- opt_mmap_sexp_list sexp_statement (EL 1 args);
         return (While expr stmts)
       od
     else if (ss = "Statement.Foreach" ∧ LENGTH args = 4) then
       do
         boundNam <- sexp_name (EL 0 args);
         boundTyp <- sexp_type (EL 1 args);
         over <- sexp_expression (EL 2 args);
         body <- opt_mmap_sexp_list sexp_statement (EL 3 args);
         return (Foreach boundNam boundTyp over body)
       od
     else if (ss = "Statement.Call" ∧ LENGTH args = 5) then
       do
         on <- sexp_expression (EL 0 args);
         callNam <- sexp_callName (EL 1 args);
         ts <- opt_mmap_sexp_list sexp_type (EL 2 args);
         exprs <- opt_mmap_sexp_list sexp_expression (EL 3 args);
         opt <- sxsym_to_opt (EL 4 args);
         ids <<- monad_bind opt (opt_mmap_sexp_list sexp_ident);
         return (Call on callNam ts exprs ids)
       od
     else if (ss = "Statement.Return" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (Return expr)
       od
     else if (ss = "Statement.EarlyReturn" ∧ LENGTH args = 0) then
       return EarlyReturn
     else if (ss = "Statement.Break" ∧ LENGTH args = 1) then
       do
         opt <- sxsym_to_opt (EL 0 args);
         toLabel <<- monad_bind opt (sxstr_to_str);
         return (Break toLabel)
       od
     else if (ss = "Statement.TailRecursive" ∧ LENGTH args = 1) then
       do
         body <- opt_mmap_sexp_list sexp_statement (EL 0 args);
         return (TailRecursive body)
       od
     else if (ss = "Statement.JumpTailCallStart" ∧ LENGTH args = 0) then
       return JumpTailCallStart
     else if (ss = "Statement.Halt" ∧ LENGTH args = 0) then
       return Halt
     else if (ss = "Statement.Print" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (Print expr)
       od
     else fail
   od
  )
Termination
  cheat
End


(* sexp -> (method option) *)
Definition sexp_method_def:
  sexp_method se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Method.Method" ∧ LENGTH args = 9);
    isStatic <- sxsym_to_bool (EL 0 args);
    hasBody <- sxsym_to_bool (EL 1 args);
    opt <- sxsym_to_opt (EL 2 args);
    overridingPath <<- monad_bind opt (opt_mmap_sexp_list sexp_ident);
    n <- sexp_name (EL 3 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 4 args);
    params <- opt_mmap_sexp_list sexp_formal (EL 5 args);
    body <- opt_mmap_sexp_list sexp_statement (EL 6 args);
    outTypes <- opt_mmap_sexp_list sexp_type (EL 7 args);
    opt <- sxsym_to_opt (EL 8 args);
    outVars <<- monad_bind opt (opt_mmap_sexp_list sexp_ident);
    return (Method isStatic hasBody overridingPath n typeParams params body
                   outTypes outVars)
  od
End


(* sexp -> (field option) *)
Definition sexp_field_def:
  sexp_field se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Field.Field" ∧ LENGTH args = 2);
    f <- sexp_formal (EL 0 args);
    opt <- sxsym_to_opt (EL 1 args);
    expr <<- monad_bind opt sexp_expression;
    return (Field f expr)
  od
End
(* TODO Add test for sexp_field *)

(* sexp -> (classItem option) *)
Definition sexp_classItem_def:
  sexp_classItem se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "ClassItem.Method" ∧ LENGTH args = 1);
    m <- sexp_method (EL 0 args);
    return (ClassItem_Method m)
  od
End


(* sexp -> (class option) *)
Definition sexp_class_def:
  sexp_class se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Class.Class" ∧ LENGTH args = 7);
    n <- sexp_name (EL 0 args);
    enclosingModule <- sexp_ident (EL 1 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 2 args);
    superClasses <- opt_mmap_sexp_list sexp_type (EL 3 args);
    fields <- opt_mmap_sexp_list sexp_field (EL 4 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 5 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 6 args);
    return (Class n enclosingModule typeParams superClasses fields body attrs)
  od
End


(* sexp -> (trait option) *)
Definition sexp_trait_def:
  sexp_trait se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Trait.Trait" ∧ LENGTH args = 4);
    n <- sexp_name (EL 0 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 1 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 2 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 3 args);
    return (Trait n typeParams body attrs)
  od
End
(* TODO Add test for sexp_trait *)

(* sexp -> (newtype option) *)
Definition sexp_newtype_def:
  sexp_newtype se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Newtype.Newtype" ∧ LENGTH args = 7);
    n <- sexp_name (EL 0 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 1 args);
    base <- sexp_type (EL 2 args);
    rnge <- sexp_newtypeRange (EL 3 args);
    witnessStmts <- opt_mmap_sexp_list sexp_statement (EL 4 args);
    opt <- sxsym_to_opt (EL 5 args);
    witnessExpr <<- monad_bind opt sexp_expression;
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 6 args);
    return (Newtype n typeParams base rnge witnessStmts witnessExpr attrs)
  od
End


(* sexp -> (datatypeDtor option) *)
Definition sexp_datatypeDtor_def:
  sexp_datatypeDtor se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "DatatypeDtor.DatatypeDtor" ∧ LENGTH args = 2);
    f <- sexp_formal (EL 0 args);
    opt <- sxsym_to_opt (EL 1 args);
    callNam <<- monad_bind opt sxstr_to_str;
    return (DatatypeDtor f callNam)
  od
End


(* sexp -> (datatypeCtor option) *)
Definition sexp_datatypeCtor_def:
  sexp_datatypeCtor se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "DatatypeCtor.DatatypeCtor" ∧ LENGTH args = 3);
    n <- sexp_name (EL 0 args);
    ctor_args <- opt_mmap_sexp_list sexp_datatypeDtor (EL 1 args);
    hasAnyArgs <- sxsym_to_bool (EL 2 args);
    return (DatatypeCtor n ctor_args hasAnyArgs)
  od
End


(* sexp -> (datatype sexp) *)
Definition sexp_datatype_def:
  sexp_datatype se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Datatype.Datatype" ∧ LENGTH args = 7);
    n <- sexp_name (EL 0 args);
    enclosingModule <- sexp_ident (EL 1 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 2 args);
    ctors <- opt_mmap_sexp_list sexp_datatypeCtor (EL 3 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 4 args);
    isCo <- sxsym_to_bool (EL 5 args);
    attr <- opt_mmap_sexp_list sexp_attribute (EL 6 args);
    return (Datatype n enclosingModule typeParams ctors body isCo attr)
  od
End


(* Defines the mutually recursive functions
   sexp_module: sexp -> (module option)
   sexp_moduleItem: sexp -> (moduleItem option) *)
Definition sexp_module_def:
  (sexp_module se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "Module.Module" ∧ LENGTH args = 3);
     n <- sexp_name (EL 0 args);
     attrs <- opt_mmap_sexp_list sexp_attribute (EL 1 args);
     opt <- sxsym_to_opt (EL 2 args);
     body <- map_opt_sexp_moduleItem opt;
     return (Module n attrs body)
   od
  )
  ∧
  (sexp_moduleItem se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "ModuleItem.Module" ∧ LENGTH args = 1) then
       do
         m <- sexp_module (EL 0 args);
         return (ModuleItem_Module m)
       od
     else if (ss = "ModuleItem.Class" ∧ LENGTH args = 1) then
       do
         cls <- sexp_class (EL 0 args);
         return (ModuleItem_Class cls)
       od
     else if (ss = "ModuleItem.Trait" ∧ LENGTH args = 1) then
       do
         trt <- sexp_trait (EL 0 args);
         return (ModuleItem_Trait trt)
       od
     else if (ss = "ModuleItem.Newtype" ∧ LENGTH args = 1) then
       do
         nt <- sexp_newtype (EL 0 args);
         return (ModuleItem_Newtype nt)
       od
     else if (ss = "ModuleItem.Datatype" ∧ LENGTH args = 1) then
       do
         dt <- sexp_datatype (EL 0 args);
         return (ModuleItem_Datatype dt)
       od
     else fail
   od
  ) ∧
  (map_sexp_moduleItem ses =
   case ses of
   | [] => return []
   | (se::rest) =>
       do
         se' <- sexp_moduleItem se;
         rest' <- map_sexp_moduleItem rest;
         return (se'::rest')
       od
  ) ∧
  (map_opt_sexp_moduleItem se_opt =
   case se_opt of
   | NONE => return NONE
   | SOME se =>
       do
         ses <- strip_sxcons se;
         mis <- map_sexp_moduleItem ses;
         return (SOME mis)
       od
  )
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL se => sexp_size se
                            | INR (INL se) => sexp_size se
                            | INR (INR (INL ses)) => list_size sexp_size ses
                            | INR (INR (INR se_opt)) => option_size sexp_size se_opt’ \\ rw[]
  \\ gvs[LENGTH_EQ_NUM_compute, oneline dstrip_sexp_def, sexp_size_def,
         AllCaseEqs(), oneline strip_sxcons_def, sexp_size_eq,
         oneline sxsym_to_opt_def, option_size_def]
End

(* sexp -> ((module list) option) *)
Definition sexp_program_def:
  (sexp_program se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "Program");
     opt_mmap_sexp_list sexp_module (EL 0 args)
   od
  )
End

val _ = export_theory();
