(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)

open preamble caml_lexTheory camlPEGTheory astTheory;

val _ = new_theory "camlPTreeConversion";

val _ = enable_monadsyntax ();
val _ = enable_monad "option";

Overload lift[local] = “option$OPTION_MAP”;

Definition ifM_def:
  ifM bM tM eM =
    do
      b <- bM;
      if b then tM else eM
    od
End

Definition mapM_def:
  mapM f [] = SOME [] ∧
  mapM f (x::xs) =
    do
      y <- f x;
      ys <- mapM f xs;
      SOME (y::ys)
    od
End

Definition destLf_def:
  destLf (Lf x) = SOME x ∧
  destLf _ = NONE
End

Definition ptree_Ident_def:
  ptree_Ident (Lf t) = NONE ∧
  ptree_Ident (Nd n args) =
    do
      assert (FST n = INL nIdent);
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- destTOK lf;
            destIdent tk
          od
      | _ => NONE
    od
End

Definition ptree_Name_def:
  ptree_Name symb =
    do
      lf <- destLf symb;
      tk <- destTOK lf;
      destIdent tk
    od
End

Definition expect_tok_def:
  expect_tok symb token =
    do
      lf <- destLf symb;
      tk <- destTOK lf;
      assert (tk = token);
      SOME tk
    od
End

Definition ptree_TVar_def:
  ptree_TVar (Lf t) = NONE ∧
  ptree_TVar (Nd n args) =
    do
      assert (FST n = INL nTVar);
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            nm <- ptree_Ident id;
            SOME (TVar nm)
          od
      | _ => NONE
    od
End

Definition ptree_TAny_def:
  ptree_TAny (Lf t) = NONE ∧
  ptree_TAny (Nd n args) =
    do
      assert (FST n = INL nTAny);
      SOME TAny
    od
End

Definition ptree_Type_def:
  (ptree_Type (Lf _) : type option = NONE) ∧
  (ptree_Type (Nd n args) =
    if FST n = INL nType then
      case args of
        [ty] => ptree_Type ty
      | _ => NONE
    else if FST n = INL nTBase then
      case args of
        [lpar; args; rpar; ctor] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ts <- ptree_TypeList args;
            nm <- ptree_Name ctor;
            SOME (TCons nm ts)
          od
      | [lpar; arg; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Type arg
          od
      | [arg] =>
          ptree_TVar arg ++ ptree_TAny arg
      | _ => NONE
    else if FST n = INL nTConstr then
      case args of
        [arg] => ptree_Type arg
      | arg::rest =>
          do
            ty <- ptree_Type arg;
            ids <- mapM ptree_Name rest;
            SOME (FOLDL (λt id. TCons id [t]) ty ids)
          od
      | _ => NONE
    else if FST n = INL nTProd then
      case args of
        [arg] => ptree_Type arg
      | [arg;star;prod] =>
          do
            expect_tok star StarT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type prod;
            SOME (TProd ty1 ty2)
          od
      | _ => NONE
    else if FST n = INL nTFun then
      case args of
        [arg] => ptree_Type arg
      | [arg;rarrow;fun] =>
          do
            expect_tok rarrow RarrowT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type fun;
            SOME (TFun ty1 ty2)
          od
      | _ => NONE
    else if FST n = INL nTAs then
      case args of
        [arg] => ptree_Type arg
      | [arg;as;tick;id] =>
          do
            expect_tok as AsT;
            expect_tok tick TickT;
            ty <- ptree_Type arg;
            nm <- ptree_Name id;
            SOME (TAs ty nm)
          od
      | _ => NONE
    else
      NONE) ∧
  (ptree_TypeList (Lf t) : type list option = NONE) ∧
  (ptree_TypeList (Nd n args) =
    if FST n = INL nTypeList then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            SOME (t::ts)
          od
      | _ => NONE
    else if FST n = INL nTypeLists then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            SOME (t::ts)
          od
      | [typ] =>
          do
            t <- ptree_Type typ;
            SOME [t]
          od
      | _ => NONE
    else
      NONE)
End

val _ = export_theory ();

