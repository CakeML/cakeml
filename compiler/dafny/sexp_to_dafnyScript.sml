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
(* TODO rename str to s *)
(* TODO update stale names referring to old sexp type *)
(* TODO? replace names sexp_<type> to sexp_to_<type> *)

Definition dstrip_sexp_def:
  dstrip_sexp (Expr ((Atom s)::rest)) = return (s, rest) ∧
  dstrip_sexp _ = fail
End

Definition strip_sxcons_def:
  strip_sxcons (Expr ses) = return ses ∧
  strip_sxcons _ = fail
End

Definition sxstr_to_str_def:
  (sxstr_to_str (Atom str) = return str) ∧
  (sxstr_to_str _ = fail)
End

Definition sxstr_to_ch_def:
  (sxstr_to_ch (Atom [c]) = return c) ∧
  (sxstr_to_ch _ = fail)
End

Definition sxnum_to_num_def:
  (sxnum_to_num (Atom s) = fromNatString (implode s)) ∧
  (sxnum_to_num _ = fail)
End

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

(* If possible, interprets the S-expression as a list and maps the given
   function over it. *)
Definition opt_mmap_sexp_list_def:
  opt_mmap_sexp_list f ses =
  do
    ses <- strip_sxcons ses;
    OPT_MMAP f ses
  od
End

(*
 * Converting S-expressions to Dafny's AST
 *)

Definition sexp_name_def:
  sexp_name se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Name.Name" ∧ LENGTH args = 1);
    str <- sxstr_to_str (EL 0 args);
    return (Name str)
  od
End

Definition sexp_varName_def:
  sexp_varName se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "VarName.VarName" ∧ LENGTH args = 1);
    str <- sxstr_to_str (EL 0 args);
    return (VarName str)
  od
End

Definition sexp_ident_def:
  sexp_ident se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Ident.Ident" ∧ LENGTH args = 1);
    n <- sexp_name (EL 0 args);
    return (Ident n)
  od
End

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
      return Primitive_Bool
    else if (ss = "Primitive.Char") then
      return Char
    else if (ss = "Primitive.Native") then
      return Native
    else fail
  od
End

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

Definition sexp_variance_def:
  sexp_variance se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "Variance.Nonvariant") then
      return Nonvariant
    else if (ss = "Variance.Covariant") then
      return Covariant
    else if (ss = "Variance.Contravariant") then
      return Contravariant
    else fail
  od
End

Definition sexp_typeParameterInfo_def:
  sexp_typeParameterInfo se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "TypeParameterInfo.TypeParameterInfo" ∧ LENGTH args = 2);
    vrnc <- sexp_variance (EL 0 args);
    nec <- sxsym_to_bool (EL 1 args);
    return (TypeParameterInfo vrnc nec)
  od
End

Definition sexp_equalitySupport_def:
  sexp_equalitySupport se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "EqualitySupport.Never") then
      return Never
    else if (ss = "EqualitySupport.ConsultTypeArguments") then
      return ConsultTypeArguments
    else fail
  od
End

Definition sexp_newtypeRange_def:
  sexp_newtypeRange se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "NewtypeRange.U8" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (U8 overflow)
      od
    else if (ss = "NewtypeRange.I8" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (I8 overflow)
      od
    else if (ss = "NewtypeRange.U16" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (U16 overflow)
      od
    else if (ss = "NewtypeRange.I16" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (I16 overflow)
      od
    else if (ss = "NewtypeRange.U32" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (U32 overflow)
      od
    else if (ss = "NewtypeRange.I32" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (I32 overflow)
      od
    else if (ss = "NewtypeRange.U64" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (U64 overflow)
      od
    else if (ss = "NewtypeRange.I64" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (I64 overflow)
      od
    else if (ss = "NewtypeRange.U128" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (U128 overflow)
      od
    else if (ss = "NewtypeRange.I128" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (I128 overflow)
      od
    else if (ss = "NewtypeRange.NativeArrayIndex" ∧ LENGTH args = 0) then
      return NativeArrayIndex
    else if (ss = "NewtypeRange.BigInt" ∧ LENGTH args = 0) then
      return BigInt
    else if (ss = "NewtypeRange.Bool" ∧ LENGTH args = 0) then
      return NewtypeRange_Bool
    else if (ss = "NewtypeRange.Sequence" ∧ LENGTH args = 0) then
      return Sequence
    else if (ss = "NewtypeRange.Map" ∧ LENGTH args = 0) then
      return NewtypeRange_Map
    else if (ss = "NewtypeRange.NoRange" ∧ LENGTH args = 0) then
      return NoRange
    else fail
  od
End

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

Definition sexp_binOp_def:
  sexp_binOp se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "BinOp.Eq" ∧ LENGTH args = 1) then
      do
        referential <- sxsym_to_bool (EL 0 args);
        return (Eq referential)
      od
    else if (ss = "BinOp.Div" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (Div overflow)
      od
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
    else if (ss = "BinOp.Plus" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (Plus overflow)
      od
    else if (ss = "BinOp.Minus" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (Minus overflow)
      od
    else if (ss = "BinOp.Times" ∧ LENGTH args = 1) then
      do
        overflow <- sxsym_to_bool (EL 0 args);
        return (Times overflow)
      od
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

Definition sexp_selectContext_def:
  sexp_selectContext se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "SelectContext.SelectContextDatatype") then
      return SelectContextDatatype
    else if (ss = "SelectContext.SelectContextGeneralTrait") then
      return SelectContextGeneralTrait
    else if (ss = "SelectContext.SelectContextClassOrObjectTrait") then
      return SelectContextClassOrObjectTrait
    else fail
  od
End

Definition sexp_traitType_def:
  sexp_traitType se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "TraitType.ObjectTrait") then
       return ObjectTrait
    else if (ss = "TraitType.GeneralTrait") then
      return GeneralTrait
    else fail
  od
End

(* Defines the mutually recursive functions sexp_resolvedType and sexp_type *)
Definition sexp_type_def:
  (sexp_type se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "Type.UserDefined" ∧ LENGTH args = 1) then
       do
         resT <- sexp_resolvedType (EL 0 args);
         return (UserDefined resT)
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
         return (Type_Map key value)
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
     else if (ss = "Type.Object" ∧ LENGTH args = 0) then
       return Object
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
  (sexp_resolvedTypeBase se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "ResolvedTypeBase.Class" ∧ LENGTH args = 0) then
       return ResolvedTypeBase_Class
     else if (ss = "ResolvedTypeBase.Datatype" ∧ LENGTH args = 2) then
       do
         eqSup <- sexp_equalitySupport (EL 0 args);
         info <- opt_mmap_sexp_list sexp_typeParameterInfo (EL 1 args);
         return (ResolvedTypeBase_Datatype eqSup info)
       od
     else if (ss = "ResolvedTypeBase.Trait" ∧ LENGTH args = 1) then
       do
         tt <- sexp_traitType (EL 0 args);
         return (ResolvedTypeBase_Trait tt)
       od
     else if (ss = "ResolvedTypeBase.SynonymType" ∧ LENGTH args = 1) then
       do
         baseT <- sexp_type (EL 0 args);
         return (ResolvedTypeBase_SynonymType baseT)
       od
     else if (ss = "ResolvedTypeBase.Newtype" ∧ LENGTH args = 3) then
       do
         baseT <- sexp_type (EL 0 args);
         rang <- sexp_newtypeRange (EL 1 args);
         erase <- sxsym_to_bool (EL 2 args);
         return (ResolvedTypeBase_Newtype baseT rang erase)
       od
     else fail
   od
  ) ∧
  (sexp_resolvedType se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "ResolvedType.ResolvedType" ∧ LENGTH args = 6);
     path <- opt_mmap_sexp_list sexp_ident (EL 0 args);
     (* TODO Should we just merge this into map_sexp_type? *)
     arg1_list <- strip_sxcons (EL 1 args);
     typeArgs <- map_sexp_type arg1_list;
     knd <- sexp_resolvedTypeBase (EL 2 args);
     attrs <- opt_mmap_sexp_list sexp_attribute (EL 3 args);
     properMethods <- opt_mmap_sexp_list sexp_name (EL 4 args);
     arg5_list <- strip_sxcons (EL 5 args);
     extendedTs <- map_sexp_type arg5_list;
     return (ResolvedType path typeArgs knd attrs properMethods extendedTs)
   od)
Termination
  cheat
  (* outdated *)
  (* WF_REL_TAC ‘measure $ λx. case x of *)
  (*                           | INL se => sexp_size se *)
  (*                           | INR (INL ses) => list_size sexp_size ses *)
  (*                           | INR (INR se) => sexp_size se’ \\ rw[] *)
  (* \\ gvs[LENGTH_EQ_NUM_compute, oneline dstrip_sexp_def, sexp_size_def, *)
  (*        AllCaseEqs(), oneline strip_sxcons_def, sexp_size_eq] *)
End

Definition sexp_typedBinOp_def:
  sexp_typedBinOp se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "TypedBinOp.TypedBinOp" ∧ LENGTH args = 4);
    op <- sexp_binOp (EL 0 args);
    leftT <- sexp_type (EL 1 args);
    rightT <- sexp_type (EL 2 args);
    resT <- sexp_type (EL 3 args);
    return (TypedBinOp op leftT rightT resT)
  od
End

Definition sexp_typeArgBound_def:
  sexp_typeArgBound se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "TypeArgBound.SupportsEquality" ∧ LENGTH args = 0) then
      return SupportsEquality
    else if (ss = "TypeArgBound.SupportsDefault" ∧ LENGTH args = 0) then
      return SupportsDefault
    else if (ss = "TypeArgBound.TraitBound" ∧ LENGTH args = 1) then
      do
        typ <- sexp_type (EL 0 args);
        return (TraitBound typ)
      od
    else fail
  od
End

Definition sexp_typeArgDecl_def:
  sexp_typeArgDecl se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "TypeArgDecl.TypeArgDecl" ∧ LENGTH args = 3);
    nam <- sexp_ident (EL 0 args);
    bounds <- opt_mmap_sexp_list sexp_typeArgBound (EL 1 args);
    info <- sexp_typeParameterInfo (EL 2 args);
    return (TypeArgDecl nam bounds info)
  od
End

Definition sexp_newtypeType_def:
  sexp_newtypeType se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "NewtypeType.NewtypeType" ∧ LENGTH args = 3);
    baseT <- sexp_type (EL 0 args);
    rang <- sexp_newtypeRange (EL 1 args);
    erase <- sxsym_to_bool (EL 2 args);
    return (NewtypeType baseT rang erase)
  od
End

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

Definition sexp_formal_def:
  sexp_formal se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Formal.Formal" ∧ LENGTH args = 3);
    n <- sexp_varName (EL 0 args);
    typ <- sexp_type (EL 1 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 2 args);
    return (Formal n typ attrs)
  od
End

Definition sexp_callSignature_def:
  sexp_callSignature se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "CallSignature.CallSignature" ∧ LENGTH args = 2);
    params <- opt_mmap_sexp_list sexp_formal (EL 0 args);
    inheritedP <- opt_mmap_sexp_list sexp_formal (EL 1 args);
    return (CallSignature params inheritedP)
  od
End

Definition sexp_callName_def:
  sexp_callName se =
  do
    (ss, args) <- dstrip_sexp se;
    if (ss = "CallName.CallName" ∧ LENGTH args = 5) then
      do
        n <- sexp_name (EL 0 args);
        (* TODO turn rhs into option/error
           return_option (sysym_to_opt ..), define using return/fail *)
        opt <- sxsym_to_opt (EL 1 args);
        typ_opt <<- monad_bind opt sexp_type;
        opt <- sxsym_to_opt (EL 2 args);
        receiverArg_opt <<- monad_bind opt sexp_formal;
        receiverAsArgument <- sxsym_to_bool (EL 3 args);
        sig <- sexp_callSignature (EL 4 args);
        return (CallName n typ_opt receiverArg_opt receiverAsArgument sig)
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

Definition sexp_fieldMutability_def:
  sexp_fieldMutability se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (LENGTH args = 0);
    if (ss = "FieldMutability.ConstantField") then
      return ConstantField
    else if (ss = "FieldMutability.InternalClassConstantFieldOrDatatypeDestructor") then
      return InternalClassConstantFieldOrDatatypeDestructor
    else if (ss = "FieldMutability.ClassMutableField") then
      return ClassMutableField
    else fail
  od
End

(* TODO Move sexp_statement to the first position in sexp_statement_def
 *
 * I have the suspicion that the name for the induction in the translator is
 *  based on what is defined first, not the name of Definition. *)

(* Defines the mutually recursive functions sexp_assignLhs, sexp_expression, and
 * sexp_statement *)
Definition sexp_statement_def:
  (sexp_assignLhs se =
   do
     (ss, args) <- dstrip_sexp se;
     if (ss = "AssignLhs.Ident" ∧ LENGTH args = 1) then
       do
         id <- sexp_varName (EL 0 args);
         return (AssignLhs_Ident id)
       od
     else if (ss = "AssignLhs.Select" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_varName (EL 1 args);
         isCnst <- sxsym_to_bool (EL 2 args);
         return (AssignLhs_Select expr field isCnst)
       od
     else if (ss = "AssignLhs.Index" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         indices <- map_sexp_expression arg1_list;
         return (AssignLhs_Index expr indices)
       od
     else fail
   od)
  ∧
  (sexp_field se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "Field.Field" ∧ LENGTH args = 4);
     f <- sexp_formal (EL 0 args);
     isCnst <- sxsym_to_bool (EL 1 args);
     opt <- sxsym_to_opt (EL 2 args);
     expr <<- monad_bind opt sexp_expression;
     isStatic <- sxsym_to_bool (EL 3 args);
     return (Field f isCnst expr isStatic)
   od)
  ∧
  (map_sexp_field ses =
   case ses of
   | [] => return []
   | (se::rest) =>
       do
         fse <- sexp_field se;
         frest <- map_sexp_field rest;
         return (fse::frest)
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
         n <- sexp_varName (EL 0 args);
         return (Expression_Ident n)
       od
     else if (ss = "Expression.Companion" ∧ LENGTH args = 2) then
       do
         ids <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 1 args);
         return (Companion ids typeArgs)
       od
     else if (ss = "Expression.ExternCompanion" ∧ LENGTH args = 1) then
       do
         ids <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         return (ExternCompanion ids)
       od
     else if (ss = "Expression.Tuple" ∧ LENGTH args = 1) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         exprs <- map_sexp_expression arg0_list;
         return (Expression_Tuple exprs)
       od
     else if (ss = "Expression.New" ∧ LENGTH args = 3) then
       do
         path <- opt_mmap_sexp_list sexp_ident (EL 0 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 1 args);
         arg2_list <- strip_sxcons (EL 2 args);
         new_args <- map_sexp_expression arg2_list;
         return (New path typeArgs new_args)
       od
     else if (ss = "Expression.NewUninitArray" ∧ LENGTH args = 2) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         dims <- map_sexp_expression arg0_list;
         typ <- sexp_type (EL 1 args);
         return (NewUninitArray dims typ)
       od
     else if (ss = "Expression.ArrayIndexToInt" ∧ LENGTH args = 1) then
       do
         val <- sexp_expression (EL 0 args);
         return (ArrayIndexToInt val)
       od
     else if (ss = "Expression.FinalizeNewArray" ∧ LENGTH args = 2) then
       do
         val <- sexp_expression (EL 0 args);
         t <- sexp_type (EL 1 args);
         return (FinalizeNewArray val t)
       od
     else if (ss = "Expression.DatatypeValue" ∧ LENGTH args = 5) then
       do
         dtType <- sexp_resolvedType (EL 0 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 1 args);
         variant <- sexp_name (EL 2 args);
         isCo <- sxsym_to_bool (EL 3 args);
         arg4_list <- strip_sxcons (EL 4 args);
         contents <- map_sxstr_to_varName_sexp_expression_tuple arg4_list;
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
         arg0_list <- strip_sxcons (EL 0 args);
         exprs <- map_sexp_expression arg0_list;
         typ <- sexp_type (EL 1 args);
         return (SeqValue exprs typ)
       od
     else if (ss = "Expression.SetValue" ∧ LENGTH args = 1) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         exprs <- map_sexp_expression arg0_list;
         return (SetValue exprs)
       od
     else if (ss = "Expression.MultisetValue" ∧ LENGTH args = 1) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         exprs <- map_sexp_expression arg0_list;
         return (MultisetValue exprs)
       od
     else if (ss = "Expression.MapValue" ∧ LENGTH args = 3) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         e_tuples <- map_sexp_expression_sexp_expression_tuple arg0_list;
         domainT <- sexp_type (EL 1 args);
         rangeT <- sexp_type (EL 2 args);
         return (MapValue e_tuples domainT rangeT)
       od
     else if (ss = "Expression.MapBuilder" ∧ LENGTH args = 2) then
       do
         keyTyp <- sexp_type (EL 0 args);
         valTyp <- sexp_type (EL 1 args);
         return (Expression_MapBuilder keyTyp valTyp)
       od
     else if (ss = "Expression.SeqUpdate" ∧ LENGTH args = 5) then
       do
         expr <- sexp_expression (EL 0 args);
         indexExpr <- sexp_expression (EL 1 args);
         v <- sexp_expression (EL 2 args);
         collT <- sexp_type (EL 3 args);
         exprT <- sexp_type (EL 4 args);
         return (SeqUpdate expr indexExpr v collT exprT)
       od
     else if (ss = "Expression.MapUpdate" ∧ LENGTH args = 5) then
       do
         expr <- sexp_expression (EL 0 args);
         indexExpr <- sexp_expression (EL 1 args);
         v <- sexp_expression (EL 2 args);
         collT <- sexp_type (EL 3 args);
         exprT <- sexp_type (EL 4 args);
         return (MapUpdate expr indexExpr v collT exprT)
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
     else if (ss = "Expression.UnOp" ∧ LENGTH args = 3) then
       do
         uOp <- sexp_unaryOp (EL 0 args);
         expr <- sexp_expression (EL 1 args);
         typ <- sexp_type (EL 2 args);
         return (UnOp uOp expr typ)
       od
     else if (ss = "Expression.BinOp" ∧ LENGTH args = 3) then
       do
         op <- sexp_typedBinOp (EL 0 args);
         left <- sexp_expression (EL 1 args);
         right <- sexp_expression (EL 2 args);
         return (BinOp op left right)
       od
     else if (ss = "Expression.ArrayLen" ∧ LENGTH args = 4) then
       do
         expr <- sexp_expression (EL 0 args);
         eT <- sexp_type (EL 1 args);
         dim <- sxnum_to_num (EL 2 args);
         native <- sxsym_to_bool (EL 3 args);
         return (ArrayLen expr eT dim native)
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
     else if (ss = "Expression.MapItems" ∧ LENGTH args = 1) then
       do
         expr <- sexp_expression (EL 0 args);
         return (MapItems expr)
       od
     else if (ss = "Expression.Select" ∧ LENGTH args = 5) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_varName (EL 1 args);
         fieldMut <- sexp_fieldMutability (EL 2 args);
         selCon <- sexp_selectContext (EL 3 args);
         fieldTyp <- sexp_type (EL 4 args);
         return (Select expr field fieldMut selCon fieldTyp)
       od
     else if (ss = "Expression.SelectFn" ∧ LENGTH args = 6) then
       do
         expr <- sexp_expression (EL 0 args);
         field <- sexp_varName (EL 1 args);
         onDatatype <- sxsym_to_bool (EL 2 args);
         isStatic <- sxsym_to_bool (EL 3 args);
         isConstant <- sxsym_to_bool (EL 4 args);
         arguments <- opt_mmap_sexp_list sexp_type (EL 5 args);
         return (SelectFn expr field onDatatype isStatic isConstant arguments)
       od
     else if (ss = "Expression.Index" ∧ LENGTH args = 3) then
       do
         expr <- sexp_expression (EL 0 args);
         cK <- sexp_collKind (EL 1 args);
         arg2_list <- strip_sxcons (EL 2 args);
         indices <- map_sexp_expression arg2_list;
         return (Index expr cK indices)
       od
     else if (ss = "Expression.IndexRange" ∧ LENGTH args = 4) then
       do
         expr <- sexp_expression (EL 0 args);
         isArray <- sxsym_to_bool (EL 1 args);
         opt <- sxsym_to_opt (EL 2 args);
         low <- opt_sexp_expression opt;
         opt <- sxsym_to_opt (EL 3 args);
         high <- opt_sexp_expression opt;
         return (IndexRange expr isArray low high)
       od
     else if (ss = "Expression.TupleSelect" ∧ LENGTH args = 4) then
       do
         expr <- sexp_expression (EL 0 args);
         index <- sxnum_to_num (EL 1 args);
         dim <- sxnum_to_num (EL 2 args);
         fieldTyp <- sexp_type (EL 3 args);
         return (TupleSelect expr index dim fieldTyp)
       od
     else if (ss = "Expression.Call" ∧ LENGTH args = 4) then
       do
         on <- sexp_expression (EL 0 args);
         callName <- sexp_callName (EL 1 args);
         typeArgs <- opt_mmap_sexp_list sexp_type (EL 2 args);
         arg3_list <- strip_sxcons (EL 3 args);
         call_args <- map_sexp_expression arg3_list;
         return (Expression_Call on callName typeArgs call_args)
       od
     else if (ss = "Expression.Lambda" ∧ LENGTH args = 3) then
       do
         params <- opt_mmap_sexp_list sexp_formal (EL 0 args);
         retTyp <- sexp_type (EL 1 args);
         arg2_list <- strip_sxcons (EL 2 args);
         body <- map_sexp_statement arg2_list;
         return (Lambda params retTyp body)
       od
     else if (ss = "Expression.BetaRedex" ∧ LENGTH args = 3) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         vs <- map_sexp_formal_sexp_expression_tuple arg0_list;
         retTyp <- sexp_type (EL 1 args);
         expr <- sexp_expression (EL 2 args);
         return (BetaRedex vs retTyp expr)
       od
     else if (ss = "Expression.IIFE" ∧ LENGTH args = 4) then
       do
         name <- sexp_varName (EL 0 args);
         typ <- sexp_type (EL 1 args);
         v <- sexp_expression (EL 2 args);
         iifeBody <- sexp_expression (EL 3 args);
         return (IIFE name typ v iifeBody)
       od
     else if (ss = "Expression.Apply" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         app_args <- map_sexp_expression arg1_list;
         return (Apply expr app_args)
       od
     else if (ss = "Expression.TypeTest" ∧ LENGTH args = 3) then
       do
         on <- sexp_expression (EL 0 args);
         dType <- opt_mmap_sexp_list sexp_ident (EL 1 args);
         vrnt <- sexp_name (EL 2 args);
         return (TypeTest on dType vrnt)
       od
     else if (ss = "Expression.Is" ∧ LENGTH args = 3) then
       do
         e <- sexp_expression (EL 0 args);
         fromT <- sexp_type (EL 1 args);
         toT <- sexp_type (EL 2 args);
         return (Is e fromT toT)
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
     else if (ss = "Expression.MapBoundedPool" ∧ LENGTH args = 1) then
       do
         of_expr <- sexp_expression (EL 0 args);
         return (MapBoundedPool of_expr)
       od
     else if (ss = "Expression.SeqBoundedPool" ∧ LENGTH args = 2) then
       do
         of_expr <- sexp_expression (EL 0 args);
         includeDuplicates <- sxsym_to_bool (EL 1 args);
         return (SeqBoundedPool of_expr includeDuplicates)
       od
     else if (ss = "Expression.MultisetBoundedPool" ∧ LENGTH args = 2) then
       do
         of_expr <- sexp_expression (EL 0 args);
         includeDuplicates <- sxsym_to_bool (EL 1 args);
         return (MultisetBoundedPool of_expr includeDuplicates)
       od
     else if (ss = "Expression.ExactBoundedPool" ∧ LENGTH args = 1) then
       do
         of_expr <- sexp_expression (EL 0 args);
         return (ExactBoundedPool of_expr)
       od
     else if (ss = "Expression.IntRange" ∧ LENGTH args = 4) then
       do
         elemT <- sexp_type (EL 0 args);
         lo <- sexp_expression (EL 1 args);
         hi <- sexp_expression (EL 2 args);
         up <- sxsym_to_bool (EL 3 args);
         return (IntRange elemT lo hi up)
       od
     else if (ss = "Expression.UnboundedIntRange" ∧ LENGTH args = 2) then
       do
         start <- sexp_expression (EL 0 args);
         up <- sxsym_to_bool (EL 1 args);
         return (UnboundedIntRange start up)
       od
     else if (ss = "Expression.Quantifier" ∧ LENGTH args = 4) then
       do
         elemT <- sexp_type (EL 0 args);
         col <- sexp_expression (EL 1 args);
         is_forall <- sxsym_to_bool (EL 2 args);
         lambda <- sexp_expression (EL 3 args);
         return (Quantifier elemT col is_forall lambda)
       od
     else fail
   od
  ) ∧
  (* Need these functions to avoid recursively passing a function to another *)
  (map_sexp_expression ses =
   case ses of
   | [] => return []
   | (se::rest) =>
       do
         fse <- sexp_expression se;
         frest <- map_sexp_expression rest;
         return (fse::frest)
       od) ∧
  (map_sexp_expression_sexp_expression_tuple ses =
   case ses of
   | [] => return []
   | ((Expr [se1; se2])::rest) =>
       do
         se1' <- sexp_expression se1;
         se2' <- sexp_expression se2;
         rest' <- map_sexp_expression_sexp_expression_tuple rest;
         return ((se1',se2')::rest')
       od
   | _ => fail) ∧
  (map_sxstr_to_varName_sexp_expression_tuple ses =
   case ses of
   | [] => return []
   | ((Expr [se1; se2])::rest) =>
       do
         se1' <- sexp_varName se1;
         se2' <- sexp_expression se2;
         rest' <- map_sxstr_to_varName_sexp_expression_tuple rest;
         return ((se1',se2')::rest')
       od
   | _ => fail) ∧
  (map_sexp_formal_sexp_expression_tuple ses =
   case ses of
   | [] => return []
   | ((Expr [se1; se2])::rest) =>
       do
         se1' <- sexp_formal se1;
         se2' <- sexp_expression se2;
         rest' <- map_sexp_formal_sexp_expression_tuple rest;
         return ((se1',se2')::rest')
       od
   | _ => fail) ∧
  (opt_sexp_expression se_opt =
   case se_opt of
   | NONE => return NONE
   | SOME se =>
       do
         se' <- sexp_expression se;
         return (SOME se')
       od
   ) ∧
  (sexp_statement se =
   do
     (ss, args) <- dstrip_sexp se;
     (* NOTE: Statement.DeclareVar is handled in map_sexp_statement *)
     if (ss = "Statement.Assign" ∧ LENGTH args = 2) then
       do
         assLhs <- sexp_assignLhs (EL 0 args);
         expr <- sexp_expression (EL 1 args);
         return (Assign assLhs expr)
       od
     else if (ss = "Statement.If" ∧ LENGTH args = 3) then
       do
         cond <- sexp_expression (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         thn <- map_sexp_statement arg1_list;
         arg2_list <- strip_sxcons (EL 2 args);
         els <- map_sexp_statement arg2_list;
         return (If cond thn els)
       od
     else if (ss = "Statement.Labeled" ∧ LENGTH args = 2) then
       do
         lbl <- sxstr_to_str (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         body <- map_sexp_statement arg1_list;
         return (Labeled lbl body)
       od
     else if (ss = "Statement.While" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         arg1_list <- strip_sxcons (EL 1 args);
         stmts <- map_sexp_statement arg1_list;
         return (While expr stmts)
       od
     else if (ss = "Statement.Foreach" ∧ LENGTH args = 4) then
       do
         boundNam <- sexp_varName (EL 0 args);
         boundTyp <- sexp_type (EL 1 args);
         over <- sexp_expression (EL 2 args);
         arg3_list <- strip_sxcons (EL 3 args);
         body <- map_sexp_statement arg3_list;
         return (Foreach boundNam boundTyp over body)
       od
     else if (ss = "Statement.Call" ∧ LENGTH args = 5) then
       do
         on <- sexp_expression (EL 0 args);
         callNam <- sexp_callName (EL 1 args);
         ts <- opt_mmap_sexp_list sexp_type (EL 2 args);
         arg3_list <- strip_sxcons (EL 3 args);
         exprs <- map_sexp_expression arg3_list;
         opt <- sxsym_to_opt (EL 4 args);
         ids <<- monad_bind opt (opt_mmap_sexp_list sexp_varName);
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
         arg0_list <- strip_sxcons (EL 0 args);
         body <- map_sexp_statement arg0_list;
         return (TailRecursive body)
       od
     else if (ss = "Statement.JumpTailCallStart" ∧ LENGTH args = 0) then
       return JumpTailCallStart
     else if (ss = "Statement.Halt" ∧ LENGTH args = 0) then
       return Halt
     else if (ss = "Statement.Print" ∧ LENGTH args = 2) then
       do
         expr <- sexp_expression (EL 0 args);
         typ <- sexp_type (EL 1 args);
         return (Print expr typ)
       od
     else if (ss = "Statement.ConstructorNewSeparator" ∧ LENGTH args = 1) then
       do
         arg0_list <- strip_sxcons (EL 0 args);
         fields <- map_sexp_field arg0_list;
         return (ConstructorNewSeparator fields)
       od
     else fail
   od)
  ∧
  map_sexp_statement ses =
  (case ses of
     | [] => return []
     | (se::rest) =>
         do
           frest <- map_sexp_statement rest;
           (* If 'se' is DeclareVar, we deviate from Dafny's definition of the
              IR and add the block where the declaration is visible to it. *)
           (ss, args) <- dstrip_sexp se;
           if (ss = "Statement.DeclareVar" ∧ LENGTH args = 3) then
             do
               n <- sexp_varName (EL 0 args);
               typ <- sexp_type (EL 1 args);
               (* TODO Extract this pattern opt <- ... out? *)
               opt <- sxsym_to_opt (EL 2 args);
               expr <- opt_sexp_expression opt;
               return [(DeclareVar n typ expr frest)]
             od
             (* 'se' is not DeclareVar, so handle it like a normal statement. *)
           else
             do
               fse <- sexp_statement se;
               return (fse::frest)
             od
         od)
Termination
  cheat
  (* may be outdated; double check *)
  (* WF_REL_TAC ‘measure $ λx. case x of *)
  (*                           | INL se => sexp_size se *)
  (*                           | INR (INL se) => sexp_size se *)
  (*                           | INR (INR (INL ses)) => list_size sexp_size ses *)
  (*                           | INR (INR (INR (INL ses))) => list_size sexp_size ses *)
  (*                           | INR (INR (INR (INR (INL ses)))) => list_size sexp_size ses *)
  (*                           | INR (INR (INR (INR (INR (INL ses))))) => list_size sexp_size ses *)
  (*                           | INR (INR (INR (INR (INR (INR (INL se_opt)))))) => option_size sexp_size se_opt *)
  (*                           | INR (INR (INR (INR (INR (INR (INR (INL se))))))) => sexp_size se *)
  (*                           | INR (INR (INR (INR (INR (INR (INR (INR ses))))))) => list_size sexp_size ses’ \\ rw[] *)
  (* \\ gvs[LENGTH_EQ_NUM_compute, oneline dstrip_sexp_def, sexp_size_def, *)
  (*        AllCaseEqs(), oneline strip_sxcons_def, sexp_size_eq, *)
  (*        oneline sxsym_to_opt_def, option_size_def] *)
End

Definition sexp_method_def:
  sexp_method se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Method.Method" ∧ LENGTH args = 14);
    (* Skip docString at first position *)
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 1 args);
    isStatic <- sxsym_to_bool (EL 2 args);
    hasBody <- sxsym_to_bool (EL 3 args);
    outVarsAreUninitFieldsToAssign <- sxsym_to_bool (EL 4 args);
    wasFunction <- sxsym_to_bool (EL 5 args);
    opt <- sxsym_to_opt (EL 6 args);
    overridingPath <<- monad_bind opt (opt_mmap_sexp_list sexp_ident);
    n <- sexp_name (EL 7 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 8 args);
    params <- opt_mmap_sexp_list sexp_formal (EL 9 args);
    inheritedParams <- opt_mmap_sexp_list sexp_formal (EL 10 args);
    arg11_list <- strip_sxcons (EL 11 args);
    body <- map_sexp_statement arg11_list;
    outTypes <- opt_mmap_sexp_list sexp_type (EL 12 args);
    opt <- sxsym_to_opt (EL 13 args);
    outVars <<- monad_bind opt (opt_mmap_sexp_list sexp_varName);
    return (Method attrs isStatic hasBody outVarsAreUninitFieldsToAssign
                   wasFunction overridingPath n typeParams params
                   inheritedParams body outTypes outVars)
  od
End

Definition sexp_classItem_def:
  sexp_classItem se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "ClassItem.Method" ∧ LENGTH args = 1);
    m <- sexp_method (EL 0 args);
    return (ClassItem_Method m)
  od
End

Definition sexp_trait_def:
  sexp_trait se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Trait.Trait" ∧ LENGTH args = 8);
    nam <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 2 args);
    traitT <- sexp_traitType (EL 3 args);
    parents <- opt_mmap_sexp_list sexp_type (EL 4 args);
    dwncstTrt <- opt_mmap_sexp_list sexp_type (EL 5 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 6 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 7 args);
    return (Trait nam typeParams traitT parents dwncstTrt body attrs)
  od
End

Definition sexp_class_def:
  sexp_class se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Class.Class" ∧ LENGTH args = 8);
    n <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    enclosingModule <- sexp_ident (EL 2 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 3 args);
    superClasses <- opt_mmap_sexp_list sexp_type (EL 4 args);
    fields <- opt_mmap_sexp_list sexp_field (EL 5 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 6 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 7 args);
    return (Class n enclosingModule typeParams superClasses fields body attrs)
  od
End

Definition sexp_newtypeConstraint_def:
  sexp_newtypeConstraint se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "NewtypeConstraint.NewtypeConstraint" ∧ LENGTH args = 2);
    vrbl <- sexp_formal (EL 0 args);
    arg1_list <- strip_sxcons (EL 1 args);
    constraintStmts <- map_sexp_statement arg1_list;
    return (NewtypeConstraint vrbl constraintStmts)
  od
End

Definition sexp_newtype_def:
  sexp_newtype se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Newtype.Newtype" ∧ LENGTH args = 11);
    n <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 2 args);
    base <- sexp_type (EL 3 args);
    rnge <- sexp_newtypeRange (EL 4 args);
    opt <- sxsym_to_opt (EL 5 args);
    cnstrnt <<- monad_bind opt sexp_newtypeConstraint;
    arg6_list <- strip_sxcons (EL 6 args);
    witnessStmts <- map_sexp_statement arg6_list;
    opt <- sxsym_to_opt (EL 7 args);
    witnessExpr <<- monad_bind opt sexp_expression;
    eqSup <- sexp_equalitySupport (EL 8 args);
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 9 args);
    clsItms <- opt_mmap_sexp_list sexp_classItem (EL 10 args);
    return (Newtype n typeParams base rnge cnstrnt
                    witnessStmts witnessExpr eqSup attrs clsItms)
  od
End

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

Definition sexp_datatypeCtor_def:
  sexp_datatypeCtor se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "DatatypeCtor.DatatypeCtor" ∧ LENGTH args = 4);
    n <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    dtor_args <- opt_mmap_sexp_list sexp_datatypeDtor (EL 2 args);
    hasAnyArgs <- sxsym_to_bool (EL 3 args);
    return (DatatypeCtor n dtor_args hasAnyArgs)
  od
End

Definition sexp_datatype_def:
  sexp_datatype se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "Datatype.Datatype" ∧ LENGTH args = 11);
    n <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    enclosingModule <- sexp_ident (EL 2 args);
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 3 args);
    ctors <- opt_mmap_sexp_list sexp_datatypeCtor (EL 4 args);
    body <- opt_mmap_sexp_list sexp_classItem (EL 5 args);
    isCo <- sxsym_to_bool (EL 6 args);
    eqSup <- sexp_equalitySupport (EL 7 args);
    attr <- opt_mmap_sexp_list sexp_attribute (EL 8 args);
    superTraitT <- opt_mmap_sexp_list sexp_type (EL 9 args);
    superTraitNegT <- opt_mmap_sexp_list sexp_type (EL 10 args);
    return (Datatype n enclosingModule typeParams ctors body isCo eqSup attr
                     superTraitT superTraitNegT)
  od
End

Definition sexp_synonymType_def:
  sexp_synonymType se =
  do
    (ss, args) <- dstrip_sexp se;
    assert (ss = "SynonymType.SynonymType" ∧ LENGTH args = 7);
    nam <- sexp_name (EL 0 args);
    (* Skip docString at second position *)
    typeParams <- opt_mmap_sexp_list sexp_typeArgDecl (EL 2 args);
    base <- sexp_type (EL 3 args);
    arg4_list <- strip_sxcons (EL 4 args);
    witnessStmts <- map_sexp_statement arg4_list;
    opt <- sxsym_to_opt (EL 5 args);
    witnessExpr <<- monad_bind opt sexp_expression;
    attrs <- opt_mmap_sexp_list sexp_attribute (EL 6 args);
    return (SynonymType nam typeParams base witnessStmts witnessExpr attrs)
  od
End

(* Defines the mutually recursive functions sexp_module and sexp_moduleItem *)
Definition sexp_module_def:
  (sexp_module se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "Module.Module" ∧ LENGTH args = 5);
     n <- sexp_name (EL 0 args);
     (* Skip docString at second position *)
     attrs <- opt_mmap_sexp_list sexp_attribute (EL 2 args);
     requiresExtern <- sxsym_to_bool (EL 3 args);
     opt <- sxsym_to_opt (EL 4 args);
     body <- map_opt_sexp_moduleItem opt;
     return (Module n attrs requiresExtern body)
   od
  ) ∧
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
     else if (ss = "ModuleItem.SynonymType" ∧ LENGTH args = 1) then
       do
         st <- sexp_synonymType (EL 0 args);
         return (ModuleItem_SynonymType st)
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

Definition sexp_program_def:
  (sexp_program se =
   do
     (ss, args) <- dstrip_sexp se;
     assert (ss = "Program" ∧ LENGTH args = 1);
     opt_mmap_sexp_list sexp_module (EL 0 args)
   od
  )
End

(* In-Logic Testing *)
(* open dafny_sexpTheory *)
(* open fromSexpTheory simpleSexpParseTheory *)
(* open TextIO *)

(* val inStream = TextIO.openIn "./tests/output/3_Calls-As.dfy.sexp"; *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)

(* val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand; *)
(* val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand; *)
(* val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand; *)

val _ = export_theory();
