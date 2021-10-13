(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)

open preamble caml_lexTheory camlPEGTheory astTheory;

val _ = new_theory "camlPtreeConversion";

(* -------------------------------------------------------------------------
 * Sum monad syntax
 * ------------------------------------------------------------------------- *)

Definition bind_def[simp]:
  bind (INL e) f = INL e ∧
  bind (INR x) f = f x
End

Definition ignore_bind_def[simp]:
  ignore_bind m1 m2 = bind m1 (λu. m2)
End

Definition choice_def[simp]:
  choice (INL e) b = b ∧
  choice (INR x) b = INR x
End

Definition return_def[simp]:
  return = INR
End

Definition fail_def[simp]:
  fail = INL
End

val sum_monadinfo : monadinfo = {
  bind = “bind”,
  ignorebind = SOME “ignore_bind”,
  unit = “return”,
  fail = SOME “fail”,
  choice = SOME “choice”,
  guard = NONE
  };

val _ = declare_monad ("sum", sum_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "sum";

Definition mapM_def:
  mapM f [] = return [] : 'a + 'b list ∧
  mapM f (x::xs) =
    do
      y <- f x;
      ys <- mapM f xs;
      return (y::ys)
    od
End

Theorem mapM_cong[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      mapM f xs: 'a + 'b list = mapM g ys
Proof
  Induct \\ rw [mapM_def]
  \\ Cases_on ‘g h’ \\ fs [mapM_def]
  \\ ‘mapM f xs = mapM g xs’ suffices_by simp_tac std_ss []
  \\ first_x_assum irule \\ fs []
QED

Definition option_def[simp]:
  option NONE = INL (unknown_loc, «option») ∧
  option (SOME x) = INR x
End

Definition fmap_def[simp]:
  fmap f (INR x) = INR (f x) ∧
  fmap f (INL err) = INL err
End

(* -------------------------------------------------------------------------
 * Parse tree conversion
 * ------------------------------------------------------------------------- *)

Definition destLf_def:
  destLf (Lf x) = return x ∧
  destLf (Nd (_, locs) _) = fail (locs, «destLf: Not a leaf»)
End

Definition expect_tok_def:
  expect_tok symb (token: token) =
    do
      lf <- destLf symb;
      tk <- option $ destTOK lf;
      if tk = token then
        return tk
      else
        fail (SND lf, «Unexpected token»)
    od
End

Definition path_to_ns_def:
  path_to_ns locs [] = fail (locs, «Empty path») ∧
  path_to_ns locs [i] = return (Short i) ∧
  path_to_ns locs [m; i] = return (Long m $ Short i) ∧
  path_to_ns locs _ = fail (locs, «Nested modules are not supported»)
End

Definition ptree_Ident_def:
  ptree_Ident (Lf (_, locs)) = fail (locs, «Expected ident non-terminal») ∧
  ptree_Ident (Nd (nterm, locs) args) =
    if nterm = INL nIdent then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nIdent»)
    else
      fail (locs, «Expected ident non-terminal»)
End

Definition ptree_OperatorName_def:
  ptree_OperatorName (Lf (_, locs)) =
    fail (locs, «Expected operator-name non-terminal») ∧
  ptree_OperatorName (Nd (nterm, locs) args) =
    if nterm = INL nOperatorName then
      case args of
        [arg] =>
          fail (locs, «Cannot use infix operators as prefix (yet)»)
      | _ => fail (locs, «Impossible: nOperatorName»)
    else
      fail (locs, «Expected operator-name non-terminal»)
End

Definition ptree_ValueName_def:
  ptree_ValueName (Lf (_, locs)) =
    fail (locs, «Expected value-name non-terminal») ∧
  ptree_ValueName (Nd (nterm, locs) args) =
    if nterm = INL nValueName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | [lpar; opn; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_OperatorName opn
          od
      | _ => fail (locs, «Impossible: nValueName»)
    else
      fail (locs, «Expected value-name non-terminal»)
End

Definition ptree_ConstrName_def:
  ptree_ConstrName (Lf (_, locs)) =
    fail (locs, «Expected constr-name non-terminal») ∧
  ptree_ConstrName (Nd (nterm, locs) args) =
    if nterm = INL nConstrName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nConstrName»)
    else
      fail (locs, «Expected constr-name non-terminal»)
End

Definition ptree_TypeConstrName_def:
  ptree_TypeConstrName (Lf (_, locs)) =
    fail (locs, «Expected typeconstr-name non-terminal») ∧
  ptree_TypeConstrName (Nd (nterm, locs) args) =
    if nterm = INL nTypeConstrName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nTypeConstrName»)
    else
      fail (locs, «Expected typeconstr-name non-terminal»)
End

Definition ptree_ModuleName_def:
  ptree_ModuleName (Lf (_, locs)) =
    fail (locs, «Expected modulename non-terminal») ∧
  ptree_ModuleName (Nd (nterm, locs) args) =
    if nterm = INL nModuleName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nModuleName»)
    else
      fail (locs, «Expected modulename non-terminal»)
End

Definition ptree_ValuePath_def:
  ptree_ValuePath (Lf (_, locs)) =
    fail (locs, «Expected value-path non-terminal») ∧
  ptree_ValuePath (Nd (nterm, locs) args) =
    if nterm = INL nValuePath then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ValueName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ValuePath path;
            vn <- ptree_ValueName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nValuePath»)
    else
      fail (locs, «Expected value-path non-terminal»)
End

Definition ptree_Constr_def:
  ptree_Constr (Lf (_, locs)) = fail (locs, «Expected constr non-terminal») ∧
  ptree_Constr (Nd (nterm, locs) args) =
    if nterm = INL nConstr then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ConstrName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_Constr path;
            vn <- ptree_ConstrName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nConstr»)
    else
      fail (locs, «Expected constr non-terminal»)
End

Definition ptree_TypeConstr_def:
  ptree_TypeConstr (Lf (_, locs)) =
    fail (locs, «Expected typeconstr non-terminal») ∧
  ptree_TypeConstr (Nd (nterm, locs) args) =
    if nterm = INL nTypeConstr then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_TypeConstrName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_TypeConstr path;
            vn <- ptree_TypeConstrName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nTypeConstr»)
    else
      fail (locs, «Expected typeconstr non-terminal»)
End

Definition ptree_ModulePath_def:
  ptree_ModulePath (Lf (_, locs)) =
    fail (locs, «Expected module-path non-terminal») ∧
  ptree_ModulePath (Nd (nterm, locs) args) =
    if nterm = INL nModulePath then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ModuleName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_ModuleName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nModulePath»)
    else
      fail (locs, «Expected module-path non-terminal»)
End

Definition ptree_TVar_def:
  ptree_TVar (Lf (_, locs)) =
    fail (locs, «Expected type variable non-terminal») ∧
  ptree_TVar (Nd (nterm, locs) args) =
    if nterm = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            nm <- ptree_Ident id;
            return (Atvar nm)
          od
      | _ => fail (locs, «Impossible: nTVar»)
    else
      fail (locs, «Expected type variable non-terminal»)
End

Definition ptree_TAny_def:
  ptree_TAny (Lf (_, locs)) =
    fail (locs, «Expected wildcard type non-terminal») ∧
  ptree_TAny (Nd (nterm, locs) args) =
    if nterm = INL nTAny then
      fail (locs, «Wildcard type variables are not supported»)
    else
      fail (locs, «Expected wildcard type variable non-terminal»)
End

Definition ptree_Type_def:
  (ptree_Type (Lf (_, locs)) =
    fail (locs, «Expected a type non-terminal»)) ∧
  (ptree_Type (Nd (nterm, locs) args) =
    if nterm = INL nType then
      case args of
        [ty] => ptree_Type ty
      | _ => fail (locs, «Impossible: nType»)
    else if nterm = INL nTBase then
      case args of
        [lpar; args; rpar; ctor] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ts <- ptree_TypeList args;
            nm <- ptree_TypeConstr ctor;
            ns <- path_to_ns locs nm;
            return (Atapp ts ns)
          od
      | [lpar; arg; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Type arg
          od
      | [arg] =>
          ptree_TVar arg ++ ptree_TAny arg
      | _ => fail (locs, «Impossible: nTBase»)
    else if nterm = INL nTConstr then
      case args of
        [arg] => ptree_Type arg
      | arg::rest =>
          do
            ty <- ptree_Type arg;
            ids <- mapM ptree_TypeConstr rest;
            cns <- mapM (path_to_ns locs) ids;
            return (FOLDL (λt id. Atapp [t] id) ty cns)
          od
      | _ => fail (locs, «Impossible: nTConstr»)
    else if nterm = INL nTProd then
      case args of
        [arg] => ptree_Type arg
      | [arg;star;prod] =>
          do
            expect_tok star StarT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type prod;
            return (Attup [ty1; ty2])
          od
      | _ => fail (locs, «Impossible: nTProd»)
    else if nterm = INL nTFun then
      case args of
        [arg] => ptree_Type arg
      | [arg;rarrow;fun] =>
          do
            expect_tok rarrow RarrowT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type fun;
            return (Atfun ty1 ty2)
          od
      | _ => fail (locs, «Impossible: nTFun»)
    else if nterm = INL nTAs then
      fail (locs, «Aliases in types are not supported»)
    else
      fail (locs, «Expected type non-terminal»)) ∧
  (ptree_TypeList (Lf (_, locs)) =
    fail (locs, «Expected a type list non-terminal»)) ∧
  (ptree_TypeList (Nd (nterm, locs) args) =
    if nterm = INL nTypeList then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | _ => fail (locs, «Impossible: nTypeList»)
    else if nterm = INL nTypeLists then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | [typ] => fmap (λt. [t]) $ ptree_Type typ
      | _ => fail (locs, «Impossible: nTypeLists»)
    else
      fail (locs, «Expected a type list non-terminal»))
End

Definition ptree_Literal_def:
  ptree_Literal (Lf (_, locs)) =
    fail (locs, «Expected a literal non-terminal») ∧
  ptree_Literal (Nd (nterm, locs) args) =
    if nterm = INL nLiteral then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if isInt tk then
              return $ IntLit $ THE $ destInt tk
            else if isChar tk then
              return $ Char $ THE $ destChar tk
            else if isString tk then
              return $ StrLit $ THE $ destString tk
            else
              fail (locs, «Impossible: nLiteral»)
          od
      | _ => fail (locs, «Impossible: nLiteral»)
    else
      fail (locs, «Expected a literal non-terminal»)
End

(* TODO
 *   There's several made-up function names here that should be replaced
 *   by code which converts from integers to 64-bit words and back.
 w   For example, CakeML.lsl a b should be:
 *
 *     App WordToInt [
 *       App (Opw Lsl) [App WordFromInt [a];
 *                      App WordFromInt [b]]]
 *)

Definition ptree_Op_def:
  ptree_Op (Lf (_, locs)) =
    fail (locs, «Expected binary operation non-terminal») ∧
  ptree_Op (Nd (nterm, locs) args) =
    case args of
      [arg] =>
        do
          lf <- destLf arg;
          tk <- option $ destTOK lf;
          if nterm = INL nShiftOp then
            if tk = LslT then
              return $ INL $ Long "CakeML" $ Short "lsl"
            else if tk = LsrT then
              return $ INL $ Long "CakeML" $ Short "lsr"
            else if tk = AsrT then
              return $ INL $ Long "CakeML" $ Short "asr"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                if s = "**" then
                  return $ INL $ Long "Double" $ Short "pow"
                else
                  return $ INL $ Short s
            else
              fail (locs, «Impossible: nShiftOp»)
          else if nterm = INL nMultOp then
            if tk = StarT then
              return $ INR $ Opn Times
            else if tk = ModT then
              return $ INR $ Opn Modulo
            else if tk = LandT then
              return $ INL $ Long "CakeML" $ Short "land"
            else if tk = LorT then
              return $ INL $ Long "CakeML" $ Short "lor"
            else if tk = LxorT then
              return $ INL $ Long "CakeML" $ Short "lxor"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                if s = "/" then
                  return $ INR $ Opn Divide
                else if s = "*." then
                  return $ INR $ FP_bop FP_Mul
                else if s = "/." then
                  return $ INR $ FP_bop FP_Div
                else
                  return $ INL $ Short s
            else
              fail (locs, «Impossible: nMultOp»)
          else if nterm = INL nAddOp then
            if tk = PlusT then
              return $ INR $ Opn Plus
            else if tk = MinusT then
              return $ INR $ Opn Minus
            else if tk = MinusFT then
              return $ INR $ FP_bop FP_Sub
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                if s = "+." then
                  return $ INR $ FP_bop FP_Add
                else
                  return $ INL $ Short s
            else
             fail (locs, «Impossible: nAddOp»)
          else if nterm = INL nRelOp then
            if tk = LessT then
              return $ INR $ Opb Lt
            else if tk = GreaterT then
              return $ INR $ Opb Gt
            else if tk = EqualT then
              return $ INR Equality
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                if s = "<=" then
                  return $ INR $ Opb Leq
                else if s = ">=" then
                  return $ INR $ Opb Geq
                else if s = "<." then
                  return $ INR $ FP_cmp FP_Less
                else if s = ">." then
                  return $ INR $ FP_cmp FP_Greater
                else if s = "<=." then
                  return $ INR $ FP_cmp FP_LessEqual
                else if s = ">=." then
                  return $ INR $ FP_cmp FP_GreaterEqual
                else
                  return $ INL $ Short s
            else
              fail (locs, «Impossible: nRelOp»)
          else if nterm = INL nAndOp then
            if tk = AndalsoT ∨ tk = AmpT then
              return $ INL $ Long "CakeML" $ Short "and"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return $ INL $ Short s
            else
              fail (locs, «Impossible: nAndOp»)
          else if nterm = INL nOrOp then
            if tk = OrelseT ∨ tk = OrT then
              return $ INL $ Long "CakeML" $ Short "or"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return $ INL $ Short s
            else
              fail (locs, «Impossible: nOrOp»)
          else
            fail (locs, «Expected binary operation non-terminal»)
        od
    | _ => fail (locs, «Expected binary operation non-terminal»)
End

(* Turns a list literal pattern “[x; y; z]” into the
 * constructor pattern “x::y::z::[]”.
 *)

Definition build_list_pat_def:
  build_list_pat =
    FOLDR (λt p. Pcon (SOME (Short "::")) [t; p])
          (Pcon (SOME (Short "[]")) [])
End

(* Builds the cartesian product of two lists (of equal length).
 *)

Definition cart_prod_def:
  cart_prod ps qs =
    FLAT (MAP (λp. ZIP (REPLICATE (LENGTH qs) p, qs)) ps)
End

(* Builds the n-ary cartesian product of n lists (of any lengths).
 *)

Definition list_cart_prod_def:
  list_cart_prod [] = [[]] ∧
  list_cart_prod (xs::xss) =
    FLAT (MAP (λx. MAP (λy. x::y) (list_cart_prod xss)) xs)
End

Overload psize[local] = “parsetree_size (K 0) (K 0) (K 0)”;

Overload p1size[local] = “parsetree1_size (K 0) (K 0) (K 0)”;

Theorem parsetree_size_lemma[local]:
  p1size = list_size psize
Proof
  rw [FUN_EQ_THM]
  \\ Induct_on ‘x’ \\ rw [list_size_def, grammarTheory.parsetree_size_def]
QED

(* The parse trees contain or-patterns. “ptree_Pattern” creates one result
 * for each alternative in a or-pattern, as if all or-patterns were pulled up
 * to the top of the tree.
 *)

Definition ptree_Pattern_def:
  (ptree_Pattern (Lf (_, locs)) =
    fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_Pattern (Nd (nterm, locs) args) =
    if nterm = INL nPAny then
      case args of
        [arg] =>
          do
            expect_tok arg AnyT;
            return [Pany]
          od
      | _ => fail (locs, «Impossible: nPAny»)
    else if nterm = INL nPBase then
      case args of
        [arg] =>
          fmap (λn. [Pvar n]) (ptree_ValueName arg) ++
          ptree_Pattern arg
      | [l; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            return [Pcon NONE []]
          od
      | [l; p; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            ptree_Pattern p
          od ++
          do
            expect_tok p DotsT;
            c1 <- ptree_Literal l;
            c2 <- ptree_Literal r;
            return [Pcon (SOME (Short "..")) [Plit c1; Plit c2]]
          od
      | [lpar; pat; colon; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ps <- ptree_Pattern pat;
            ty <- ptree_Type typ;
            return (MAP (λp. Ptannot p ty) ps)
          od
      | _ => fail (locs, «Impossible: nPBase»)
    else if nterm = INL nPList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            pats <- ptree_PatternList rest;
            return (MAP build_list_pat (list_cart_prod pats))
          od
      | _ => fail (locs, «Impossible: nPList»)
    else if nterm = INL nPLazy then
      case args of
        [pat] => ptree_Pattern pat
      | [lazy; pat] =>
          do
            expect_tok lazy LazyT;
            ps <- ptree_Pattern pat;
            return (MAP (λp. Pcon (SOME (Short "lazy")) [p]) ps)
          od
      | _ => fail (locs, «Impossible: nPLazy»)
    else if nterm = INL nPConstr then
      case args of
        [pat] => ptree_Pattern pat
      | [id; pat] =>
          do
            cns <- ptree_Constr id;
            id <- path_to_ns locs cns;
            ps <- ptree_Pattern pat;
            return (MAP (λp. Pcon (SOME id) [p]) ps)
          od
      | _ => fail (locs, «Impossible: nPConstr»)
    else if nterm = INL nPApp then
      case args of
        [pat] => ptree_Pattern pat
      | _ => fail (locs, «Impossible: nPApp»)
    else if nterm = INL nPCons then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; colons; p2] =>
          do
            expect_tok colons ColonT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (MAP (λ(p,q). Pcon (SOME (Short "::")) [p; q])
                        (cart_prod ps qs))
          od
      | _ => fail (locs, «Impossible: nPCons»)
    else if nterm = INL nPProd then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; comma; p2] =>
          do
            expect_tok comma CommaT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (MAP (λ(p,q). Pcon (SOME (Short ",")) [p; q])
                        (cart_prod ps qs))
          od
      | _ => fail (locs, «Impossible: nPProd»)
    else if nterm = INL nPOr then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; bar; p2] =>
          do
            expect_tok bar BarT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (ps ++ qs)
          od
      | _ => fail (locs, «Impossible: nPOr»)
    else if nterm = INL nPAs then
      case args of
        [pat] => ptree_Pattern pat
      | [pat; ast; id] => fail (locs, «Pattern aliases are not supported»)
      | _ => fail (locs, «Impossible: nPAs»)
    else if nterm = INL nPattern then
      case args of
        [pat] => ptree_Pattern pat
      | _ => fail (locs, «Impossible: nPattern»)
    else
      fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_PatternList [] =
    fail (unknown_loc, «Pattern lists cannot be empty»)) ∧
  (ptree_PatternList [t] =
     do
       expect_tok t RbrackT;
       return []
     od) ∧
  (ptree_PatternList (p::ps) =
     do
       q <- ptree_Pattern p;
       qs <- ptree_PatternList ps;
       return (q::qs)
     od)
Termination
  WF_REL_TAC ‘measure (sum_size psize (list_size psize))’
  \\ simp [parsetree_size_lemma]
End

Definition ptree_Patterns_def:
  ptree_Patterns (Lf (_, locs)) =
    fail (locs, «Expected pattern list non-terminal») ∧
  ptree_Patterns (Nd (nterm, locs) args) =
    if nterm = INL nPatterns then
      case args of
        [pat] => fmap (λp. [p]) $ ptree_Pattern pat
      | [pat; rest] =>
          do
            p <- ptree_Pattern pat;
            ps <- ptree_Patterns rest;
            return (p::ps)
          od
      | _ => fail (locs, «Impossible: nPatterns»)
    else
      fail (locs, «Expected pattern list non-terminal»)
End

(* Builds a binary operation based on the output from “ptree_Op”.
 *)

Definition build_binop_def:
  build_binop (INR opn) x y = App opn [x; y] ∧
  build_binop (INL symb) x y = App Opapp [App Opapp [Var symb; x]; y]
End

(* Turns a list literal expression “[x; y; z]” into the
 * constructor application “x::y::z::[]”.
 *)

Definition build_list_exp_def:
  build_list_exp =
    FOLDR (λt e. Con (SOME (Short "::")) [t; e])
          (Con (SOME (Short "[]")) [])
End

Definition build_funapp_def:
  build_funapp f xs = FOLDL (λa b. App Opapp [a; b]) f xs
End

(* Turns a curried lambda with patterns, e.g. “fun a [3;4] c -> e”
 * into a sequence of lambdas, possibly with pattern matches:
 * “fun a -> fun fresh -> match fresh with [3;4] -> fun c -> e”.
 *)

Definition build_fun_lam_def:
  build_fun_lam body pats =
      FOLDR (λp b. case p of
                     Pvar x => Fun x b
                   | _ => Fun "" (Mat (Var (Short "")) [p, b]))
            body pats
End

(* Builds a letrec out of a list of let rec-bindings.
 *)

Definition build_letrec_def:
  build_letrec binds body =
    Letrec (MAP (λ(f,ps,x). (f,"",Mat (Var (Short ""))
                                    case ps of
                                      [] => [] (* this should never happen *)
                                    | p::ps =>
                                        [p, build_fun_lam x ps]))
                binds)
           body
End

(* Builds a sequence of lets out of a list of let bindings.
 *)

Definition build_lets_def:
  build_lets binds body =
    FOLDR (λbind rest.
             case bind of
               INL (p,x) =>
                 Mat x [p, rest]
             | INR (f,ps,x) =>
                 Let (SOME f) (build_fun_lam x ps) rest)
          binds body
End

(* TODO
 * With these functions it's not possible to mix value definitions
 * and recursive function definitions.
 *)

(* Builds a pattern match for a match expression. The third part of each tuple
 * is SOME when there's a guard-expression present. Each guard expression
 * duplicates the rest of the match expression.
 *
 *)

Definition build_pmatch_def:
  build_pmatch bv cn [] = [] ∧
  build_pmatch bv cn ((pat,body,NONE)::rest) =
    (pat,body)::build_pmatch bv cn rest ∧
  build_pmatch bv cn ((pat,body,SOME guard)::rest) =
    let rs = build_pmatch bv cn rest in
      (pat,If guard body (cn (Var (Short bv)) rs))::rs
End

Definition build_match_def:
  build_match bv pmatch x =
    Let (SOME bv) x (Mat (Var (Short bv)) (build_pmatch bv Mat pmatch))
End

Definition build_handle_def:
  build_handle bv pmatch x =
    Let (SOME bv) x (Handle (Var (Short bv)) (build_pmatch bv Handle pmatch))
End

Definition build_function_def:
  build_function bv pmatch =
    Fun bv (Mat (Var (Short bv)) (build_pmatch bv Mat pmatch))
End

(* Turn a boolean literal into a constructor expression.
 *)

Definition bool_to_exp_def:
  bool_to_exp b = Con (SOME (Short (if b then "True" else "False"))) []
End

(* Flatten the row-alternatives in a pattern-match.
 *)

Definition flatten_pmatch_def:
  flatten_pmatch pss = FLAT (MAP (λ(ps,x,w). MAP (λp. (p,x,w)) ps) pss)
End

Theorem list_size_lemma[local]:
  MEM x xs ⇒ m x < list_size m xs
Proof
  Induct_on ‘xs’ \\ rw [list_size_def]
  \\ res_tac \\ fs []
QED

(*
Definition ptree_linfix_def:
  ptree_linfix (topnt: camlNT) opn elnt pt =
    case pt of
      Lf _ => fail (unknown_loc, «Found nothing: ptree_linfix»)
    | Nd (nterm, locs) args =>
        if nterm = INL topnt then
          case args of
            [pt] => fmap (λx. [x]) (elnt pt)
          | [x; op_pt; pt] =>
              do
                expect_tok op_pt opn;
                front <- ptree_linfix topnt opn elnt x;
                last <- elnt pt;
                return (front ++ [last])
              od
          | _ => fail (locs, «Impossible: ptree_linfix»)
        else
          fail (locs, «Found nothing: ptree_linfix»)
End
 *)

Definition ptree_Expr_def:
  (ptree_Expr et (Lf (_, locs)) =
    fail (locs, «Expected an expression non-terminal»)) ∧
  (ptree_Expr et (Nd (nterm, locs) args) =
    if INL et ≠ nterm then
      fail (locs, concat [«expected: »; camlNT2string et; «\n»;
                          «found: »; (case nterm of INL n =>
                                        camlNT2string n
                                      | _ => «unknown»);])
    else if nterm = INL nExpr then
      case args of
        [arg] =>
          ptree_Expr nESeq arg ++
          ptree_Expr nELet arg ++
          ptree_Expr nELet arg ++
          ptree_Expr nELetRec arg ++
          ptree_Expr nEMatch arg ++
          ptree_Expr nEFun arg ++
          ptree_Expr nEFunction arg ++
          ptree_Expr nETry arg ++
          ptree_Expr nEWhile arg ++
          ptree_Expr nEFor arg ++
          fail (locs, «Expected an expression non-terminal»)
      | _ => fail (locs, «Impossible: nExpr»)
    else if nterm = INL nEList then
      case args of
        [lbrack; expr; exprs; rbrack] =>
          do
            expect_tok lbrack LbrackT;
            expect_tok rbrack RbrackT;
            x <- ptree_Expr nExpr expr;
            xs <- ptree_ESemiSep exprs;
            return (build_list_exp (x::xs))
          od
      | _ => fail (locs, «Impossible: nEList»)
    else if nterm = INL nEBase then
      case args of
        [lpar;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            return (Con NONE [])
          od
      | [lpar;expr;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Expr nExpr expr
          od ++
          do
            expect_tok lpar BeginT;
            expect_tok rpar EndT;
            ptree_Expr nExpr expr
          od
      | [lpar;expr;colon;typ;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ty <- ptree_Type typ;
            x <- ptree_Expr nExpr expr;
            return (Tannot x ty)
          od
      | [arg] =>
          fmap Lit (ptree_Literal arg) ++
          do
            cns <- ptree_ValuePath arg;
            ns <- path_to_ns locs cns;
            return (Var ns)
          od ++
          do
            cns <- ptree_Constr arg;
            ns <- path_to_ns locs cns;
            return (Con (SOME ns) [])
          od ++
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if tk = TrueT ∨ tk = FalseT then
              return (bool_to_exp (tk = TrueT))
            else
              fail (unknown_loc, «»)
          od ++
          ptree_Expr nEList arg
      | _ => fail (locs, «Impossible: nEBase»)
    else if nterm = INL nEAssert then
      case args of
        [assr; expr] =>
          do
            expect_tok assr AssertT;
            x <- ptree_Expr nEBase expr;
            return (App Opapp [Var (Short "assert"); x])
          od
      | _ => fail (locs, «Impossible: nEAssert»)
    else if nterm = INL nELazy then
      case args of
        [lazy; expr] =>
          do
            expect_tok lazy LazyT;
            x <- ptree_Expr nEBase expr;
            return (App Opapp [Var (Short "lazy"); x])
          od
      | _ => fail (locs, «Impossible: nELazy»)
    else if nterm = INL nEConstr then
      case args of
        [consid; expr] =>
          do
            cns <- ptree_Constr consid;
            id <- path_to_ns locs cns;
            x <- ptree_Expr nEBase expr;
            return (Con (SOME id) [x])
          od
      | _ => fail (locs, «Impossible: nEConstr»)
    else if nterm = INL nEFunapp then
      case args of
        [fexp; aexp] =>
          do
            f <- ptree_Expr nEBase fexp;
            x <- ptree_Expr nEBase aexp;
            return (build_funapp f [x])
          od
      | [fexp; aexp; fexps] =>
          do
            f <- ptree_Expr nEBase fexp;
            x <- ptree_Expr nEBase aexp;
            y <- ptree_Expr nEFunapp fexps;
            return (build_funapp f [x; y])
          od
      | _ => fail (locs, «Impossible: nEFunapp»)
    else if nterm = INL nEApp then
      case args of
        [arg] =>
          ptree_Expr nELazy arg ++
          ptree_Expr nEAssert arg ++
          ptree_Expr nEConstr arg ++
          ptree_Expr nEFunapp arg ++
          ptree_Expr nEBase arg
      | _ => fail (locs, «Impossible: nEApp»)
    else if nterm = INL nEPrefix then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            sym <- option $ destSymbol tk;
            x <- ptree_Expr nEApp expr;
            return (App Opapp [Var (Short sym); x])
          od
      | [arg] => ptree_Expr nEApp arg
      | _ => fail (locs, «Impossible: nEPrefix»)
    else if nterm = INL nENeg then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            x <- ptree_Expr nEPrefix expr;
            if tk = MinusT then
              return (App (Opn Minus) [Lit (IntLit 0i); x])
            else if tk = MinusFT then
              return (App (FP_bop FP_Sub) [Lit (Word64 0w); x])
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return (App Opapp [Var (Short s); x])
            else
              fail (locs, «Impossible: nEPrefix»)
          od
      | [arg] => ptree_Expr nEPrefix arg
      | _ => fail (locs, «Impossible: nEPrefix»)
    else if nterm = INL nEShift then
      case args of
        [exp] => ptree_Expr nENeg exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nENeg lhs;
            y <- ptree_Expr nEShift rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEShift»)
    else if nterm = INL nEMult then
      case args of
        [exp] => ptree_Expr nEShift exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEMult lhs;
            y <- ptree_Expr nEShift rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nMult»)
    else if nterm = INL nEAdd then
      case args of
        [exp] => ptree_Expr nEMult exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEAdd lhs;
            y <- ptree_Expr nEMult rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEAdd»)
    else if nterm = INL nECons then
      case args of
        [exp] => ptree_Expr nEAdd exp
      | [lhs; colons; rhs] =>
          do
            expect_tok colons ColonsT;
            x <- ptree_Expr nEAdd lhs;
            y <- ptree_Expr nECons rhs;
            return (Con (SOME (Short "::")) [x; y])
          od
      | _ => fail (locs, «Impossible: nECons»)
    else if nterm = INL nECat then
      case args of
        [exp] => ptree_Expr nECons exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nECons lhs;
            y <- ptree_Expr nECat rhs;
            return (build_funapp (Var (Long "String" (Short [CHR 94]))) [x; y])
          od
      | _ => fail (locs, «Impossible: nECat»)
    else if nterm = INL nERel then
      case args of
        [exp] => ptree_Expr nECat exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nERel lhs;
            y <- ptree_Expr nECat rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nERel»)
    else if nterm = INL nEAnd then
      case args of
        [exp] => ptree_Expr nERel exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nERel lhs;
            y <- ptree_Expr nEAnd rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEAnd»)
    else if nterm = INL nEOr then
      case args of
        [exp] => ptree_Expr nEAnd exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEAnd lhs;
            y <- ptree_Expr nEOr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEOr»)
    else if nterm = INL nEProd then
      case args of
        [exp] => ptree_Expr nEOr exp
      | [lhs; comma; rhs] =>
          do
            expect_tok comma CommaT;
            x <- ptree_Expr nEOr lhs;
            y <- ptree_Expr nEProd rhs;
            return (Con (SOME (Short ",")) [x; y])
          od
      | _ => fail (locs, «Impossible: nEProd»)
    else if nterm = INL nEIf then
      case args of
        [ift; x; thent; y; elset; z] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            expect_tok elset ElseT;
            x1 <- ptree_Expr nEProd x;
            y1 <- ptree_Expr nEProd y;
            z1 <- ptree_Expr nEProd z;
            return (If x1 y1 z1)
          od
      | [ift; x; thent; y] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            x1 <- ptree_Expr nEProd x;
            y1 <- ptree_Expr nEProd y;
            return (If x1 y1 (Con NONE []))
          od
      | [exp] => ptree_Expr nEProd exp
      | _ => fail (locs, «Impossible: nEIf»)
    else if nterm = INL nESeq then
      case args of
        [x; semi; y] =>
          do
            expect_tok semi SemiT;
            x1 <- ptree_Expr nEIf x;
            y1 <- ptree_Expr nESeq y;
            return (Let NONE x1 y1)
          od
      | [x] => ptree_Expr nEIf x
      | _ => fail (locs,«Impossible: nESeq»)
    else if nterm = INL nELet then
      case args of
        [lett; rec; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok rec RecT;
            expect_tok int InT;
            binds <- ptree_LetRecBindings binds;
            body <- ptree_Expr nExpr expr;
            return (build_letrec binds body)
          od
      | [lett; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok int InT;
            binds <- ptree_LetBindings binds;
            body <- ptree_Expr nExpr expr;
            return (build_lets body binds)
          od
      | _ => fail (locs, «Impossible: nELet»)
    else if nterm = INL nEMatch then
      case args of
        [match; expr; witht; pmatch] =>
          do
            expect_tok match MatchT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- ptree_PatternMatch pmatch;
            return (build_match "" (flatten_pmatch ps) x)
          od
      | _ => fail (locs, «Impossible: nEMatch»)
    else if nterm = INL nEFun then
      case args of
        [funt; params; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr nExpr expr;
            return (Fun "" (Mat (Var (Short ""))
                           (MAP (λps. case ps of
                                        [] => (Pany, Var (Short ""))
                                      | p::ps =>
                                              (p, build_fun_lam x ps))
                                ps)))
          od
      | [funt; params; colon; typ; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr nExpr expr;
            ty <- ptree_Type typ;
            return (Tannot (Fun "" (Mat (Var (Short ""))
                                   (MAP (λps. case ps of
                                                      (* this never happens:*)
                                                [] => (Pany, Var (Short ""))
                                              | p::ps =>
                                                  (p, build_fun_lam x ps))
                                        ps))) ty)
          od
      | _ => fail (locs, «Impossible: nEFun»)
    else if nterm = INL nEFunction then
      case args of
        [funct; pmatch] =>
          do
            expect_tok funct FunctionT;
            ps <- ptree_PatternMatch pmatch;
            return (build_function "" (flatten_pmatch ps))
          od
      | _ => fail (locs, «Impossible: nEFunction»)
    else if nterm = INL nETry then
      case args of
        [tryt; expr; witht; pmatch] =>
          do
            expect_tok tryt TryT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- return []; (* ptree_PatternMatch pmatch; *)
            return (build_handle "" (flatten_pmatch ps) x)
          od
      | _ => fail (locs, «Impossible: nETry»)
    else if nterm = INL nEWhile then
      case args of
        [while; expr; dot; body; donet] =>
          do
            expect_tok while WhileT;
            expect_tok dot DoT;
            expect_tok donet DoneT;
            x <- ptree_Expr nExpr expr;
            b <- ptree_Expr nExpr body;
            return (build_funapp (Var (Short "while")) [x; b])
          od
      | _ => fail (locs, «Impossible: nEWhile»)
    else if nterm = INL nEFor then
      case args of
        [for; ident; eq; ubd; updown; lbd; dot; body; donet] =>
          do
            expect_tok for ForT;
            expect_tok eq EqualT;
            expect_tok dot DoT;
            lf <- destLf updown;
            tk <- option $ destTOK lf;
            (if tk = ToT ∨ tk = DowntoT then return () else
              fail (locs, «Expected 'to' or 'downto'»));
            id <- ptree_ValueName ident;
            u <- ptree_Expr nExpr ubd;
            l <- ptree_Expr nExpr lbd;
            b <- ptree_Expr nExpr body;
            return (build_funapp (Var (Short "for"))
                                 [bool_to_exp (tk = ToT);
                                  Var (Short id); u; l; b])
          od
      | _ => fail (locs, «Impossible: nEFor»)
    else
      fail (locs, «Expected a for non-terminal»)) ∧
  (ptree_LetRecBinding (Lf (_, locs)) =
    fail (locs, «Expected a let rec binding non-terminal»)) ∧
  (ptree_LetRecBinding (Nd (nterm, locs) args) =
    if nterm = INL nLetRecBinding then
      case args of
        [id; pats; colon; type; eq; expr] =>
          do
            expect_tok colon ColonT;
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr expr;
            case ps of
              [p] => return (nm, p, Tannot bd ty)
            | _ =>
                fail (locs, «Or-patterns are not allowed in let rec bindings»)
          od
      | [id; pats; eq; expr] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            bd <- ptree_Expr nExpr expr;
            case ps of
              [p] => return (nm, p, bd)
            | _ =>
              fail (locs, «Or-patterns are not allowed in let rec bindings»)
          od
      | _ => fail (locs, «Impossible: nLetRecBinding»)
    else
      fail (locs, «Expected a let rec binding non-terminal»)) ∧
  (ptree_LetRecBindings (Lf (_, locs)) =
      fail (locs, «Expected a list of let rec bindings non-terminal»)) ∧
  (ptree_LetRecBindings (Nd (nterm, locs) args) =
    if nterm = INL nLetRecBindings then
      case args of
        [rec] =>
          fmap (λr. [r]) $ ptree_LetRecBinding rec
      | [rec; andt; recs] =>
          do
            expect_tok andt AndT;
            r <- ptree_LetRecBinding rec;
            rs <- ptree_LetRecBindings recs;
            return (r::rs)
          od
      | _ => fail (locs, «Impossible: nLetRecBindings»)
    else
      fail (locs, «Expected a list of let rec bindings non-terminal»)) ∧
  (ptree_LetBinding (Lf (_, locs)) =
    fail (locs, «Expected a let binding non-terminal»)) ∧
  (ptree_LetBinding (Nd (nterm, locs) args) =
    if nterm = INL nLetBinding then
      case args of
        [pat; eq; bod] =>
          do
            expect_tok eq EqualT;
            ps <- ptree_Pattern pat;
            x <- ptree_Expr nExpr bod;
            case ps of
              [p] => return (INL (p, x))
            | _ =>
              fail (locs, «Or-patterns are not allowed in let bindings»)
          od
      | [id; pats; eq; bod] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            x <- ptree_Expr nExpr bod;
            case ps of
              [p] => return (INR (nm, p, x))
            | _ =>
              fail (locs, «Or-patterns are not allowed in let bindings»)
          od
      | [id; pats; colon; typ; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            if EVERY (λp. LENGTH p = 1) ps then INR () else
              fail (locs, «Or-patterns are not allowed in let bindings»);
            x <- ptree_Expr nExpr bod;
            return (INR (nm, MAP (λp. case p of [] => Pany | p::_ => p) ps, x))
          od
      | _ => fail (locs, «Impossible: nLetBinding»)
    else
      fail (locs, «Expected a let binding non-terminal»)) ∧
  (ptree_LetBindings (Lf (_, locs)) =
     fail (locs, «Expected a list of let bindings non-terminal»)) ∧
  (ptree_LetBindings (Nd (nterm, locs) args) =
    if nterm = INL nLetBindings then
      case args of
        [letb] =>
          fmap (λl. [l]) $ ptree_LetBinding letb
      | [letb; andt; lets] =>
          do
            expect_tok andt AndT;
            r <- ptree_LetBinding letb;
            rs <- ptree_LetBindings lets;
            return (r::rs)
          od
      | _ => fail (locs, «Impossible: nLetBindings»)
    else
      fail (locs, «Expected a list of let bindings non-terminal»)) ∧
  (ptree_PatternMatches (Lf (_, locs)) =
    fail (locs, «Expected a pattern-matches non-terminal»)) ∧
  (ptree_PatternMatches (Nd (nterm, locs) args) =
    if nterm = INL nPatternMatches then
      case args of
        (* urk: these cases overlap *)
        [a; b; c; d; e] =>
          let pat = a; whent = b; whenx = c; rarrow = d; body = e in
            do
              expect_tok rarrow RarrowT;
              expect_tok whent WhenT;
              p <- ptree_Pattern pat;
              x <- ptree_Expr nExpr body;
              w <- ptree_Expr nExpr whenx;
              return [p, x, SOME w]
            od ++
          let pat = a; rarrow = b; body = c; bar = d; pms = e in
            do
              expect_tok rarrow RarrowT;
              p <- ptree_Pattern pat;
              x <- ptree_Expr nExpr body;
              expect_tok bar BarT;
              ps <- ptree_PatternMatch pms;
              return ((p, x, NONE)::ps)
            od
      | [pat; whent; whenx; rarrow; body; bar; pms] =>
          do
            expect_tok rarrow RarrowT;
            expect_tok whent WhenT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr nExpr body;
            w <- ptree_Expr nExpr whenx;
            expect_tok bar BarT;
            ps <- ptree_PatternMatches pms;
            return ((p, x, SOME w)::ps)
          od
      | [pat; rarrow; body] =>
          do
            expect_tok rarrow RarrowT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr nExpr body;
            return [p, x, NONE]
          od
      | _ => fail (locs, «Impossible: nPatternMatches»)
    else
      fail (locs, «Expected a pattern-matches non-terminal»)) ∧
  (ptree_PatternMatch (Lf (_, locs)) =
    fail (locs, «Expected a pattern-match non-terminal»)) ∧
  (ptree_PatternMatch (Nd (nterm, locs) args) =
    if nterm = INL nPatternMatch then
      case args of
        [bar; pms] =>
          do
            expect_tok bar BarT;
            ptree_PatternMatches pms
          od
      | [pms] => ptree_PatternMatches pms
      | _ => fail (locs, «Impossible: nPatternMatch»)
    else
      fail (locs, «Expected a pattern-match non-terminal»)) ∧
  (ptree_ESemiSep (Lf (_, locs)) =
    fail (locs, «Expected a semicolon separated expressions non-terminal»)) ∧
  (ptree_ESemiSep (Nd (nterm, locs) args) =
    if nterm = INL nESemiSep then
      case args of
        [semi] =>
          do
            expect_tok semi SemiT;
            return []
          od
      | [semi; expr] =>
          do
            expect_tok semi SemiT;
            x <- ptree_Expr nExpr expr;
            return [x]
          od
      | [semi; expr; exprs] =>
          do
            expect_tok semi SemiT;
            x <- ptree_Expr nExpr expr;
            xs <- ptree_ESemiSep exprs;
            return (x::xs)
          od
      | _ => fail (locs, «Impossible: nESemiSep»)
    else
      fail (locs, «Expected a semicolon separated expressions non-terminal»))
End

(* Tidy up the list bits of the induction theorem.
 *)

Theorem ptree_Expr_ind = ptree_Expr_ind |> SIMP_RULE (srw_ss() ++ CONJ_ss) [];

Definition ptree_StarTypes_def:
  ptree_StarTypes [] = return [] ∧
  ptree_StarTypes (x::xs) =
    do
      expect_tok x StarT;
      ptree_StarTypes xs
    od ++
    do
      t <- ptree_Type x;
      ts <- ptree_StarTypes xs;
      return (t::ts)
    od
End

Definition ptree_ConstrArgs_def:
  ptree_ConstrArgs (Lf (_, locs)) =
    fail (locs, «Expected a constructor arguments non-terminal») ∧
  ptree_ConstrArgs (Nd (nterm, locs) args) =
    if nterm = INL nConstrArgs then
      case args of
        ty::rest =>
          do
            t <- ptree_Type ty;
            ts <- ptree_StarTypes rest;
            return (t::ts)
          od
      | _ => fail (locs, «Impossible: nConstrArgs»)
    else
      fail (locs, «Expected a constructor arguments non-terminal»)
End

Definition ptree_ConstrDecl_def:
  ptree_ConstrDecl (Lf (_, locs)) =
    fail (locs, «Expected a constructor declaration non-terminal») ∧
  ptree_ConstrDecl (Nd (nterm, locs) args) =
    if nterm = INL nConstrDecl then
      case args of
        [name] =>
          fmap (λnm. (nm,[])) $ ptree_ConstrName name
      | [name; oft; args] =>
          do
            expect_tok oft OfT;
            nm <- ptree_ConstrName name;
            ts <- ptree_ConstrArgs args;
            return (nm, ts)
          od
      | _ => fail (locs, «Impossible: nConstrDecl»)
    else
      fail (locs, «Expected a constructor declaration non-terminal»)
End

Definition ptree_ExcDefinition_def:
  ptree_ExcDefinition (Lf (_, locs)) =
    fail (locs, «Expected an exception definition non-terminal») ∧
  ptree_ExcDefinition (Nd (nterm, locs) args) =
    if nterm = INL nExcDefinition then
      case args of
        [exnt; cdecl] =>
          do
            expect_tok exnt ExceptionT;
            (nm, args) <- ptree_ConstrDecl cdecl;
            return (Dexn locs nm args)
          od
      | [exnt; lhsid; eq; rhsid] =>
          do
            expect_tok exnt ExceptionT;
            expect_tok eq EqualT;
            lhs <- ptree_ConstrName lhsid;
            cns <- ptree_Constr rhsid;
            rhs <- path_to_ns locs cns;
            return (Dexn locs lhs [Atapp [] rhs])
          od
      | _ => fail (locs, «Impossible: nExcDefinition»)
    else
      fail (locs, «Expected an exception definition non-terminal»)
End

(* ptree_TypeRepr picks out constructor declarations and returns
 * a list of (constructor_name # argument_types) pairs, one for
 * each constructor.
 *)

Definition ptree_TypeRepr_def:
  ptree_TypeRepr (Lf (_, locs)) =
    fail (locs, «Expected a type-repr non-terminal») ∧
  ptree_TypeRepr (Nd (nterm, locs) args) =
    if nterm = INL nTypeRepr then
      case args of
        [bart; cdecl; reprs] =>
          do
            expect_tok bart BarT;
            tr <- ptree_ConstrDecl cdecl;
            trs <- ptree_TypeRepr reprs;
            return (tr::trs)
          od
      | [a; b] =>
          do
            expect_tok a BarT;
            tr <- ptree_ConstrDecl b;
            return [tr]
          od ++
          do
            tr <- ptree_ConstrDecl a;
            trs <- ptree_TypeRepr b;
            return (tr::trs)
          od
      | [cdecl] =>
          do
            tr <- ptree_ConstrDecl cdecl;
            return [tr]
          od
      | _ => fail (locs, «Impossible: nTypeRepr»)
    else if nterm = INL nTypeRepr then
      case args of
        [bart; cdecl] =>
          do
            expect_tok bart BarT;
            ts <- ptree_ConstrDecl cdecl;
            return [ts]
          od
      | [bart; cdecl; tyreps] =>
          do
            expect_tok bart BarT;
            ts <- ptree_ConstrDecl cdecl;
            trs <- ptree_TypeRepr tyreps;
            return (ts::trs)
          od
      | _ => fail (locs, «Impossible: nTypeReprs»)
    else
      fail (locs, «Expected a type-repr non-terminal»)
End

Definition ptree_TypeInfo_def:
  ptree_TypeInfo (Lf (_, locs)) =
    fail (locs, «Expected a type-info non-terminal») ∧
  ptree_TypeInfo (Nd (nterm, locs) args) =
    if nterm = INL nTypeInfo then
      case args of
        [tr] =>
          fmap INR $ ptree_TypeRepr tr
      | [eq; ty] =>
          do
            expect_tok eq EqualT;
            fmap INL $ ptree_Type ty
          od
      | _ => fail (locs, «Impossible: nTypeInfo»)
    else
      fail (locs, «Expected a type-info non-terminal»)
End

Definition ptree_TypeName_def:
  ptree_TypeName (Lf (_, locs)) =
    fail (locs, «Expected type variable non-terminal») ∧
  ptree_TypeName (Nd (nterm, locs) args) =
    if nterm = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            ptree_Ident id
          od
      | _ => fail (locs, «Impossible: nTVar»)
    else
      fail (locs, «Expected type variable non-terminal»)
End

Definition ptree_TypeParamList_def:
  ptree_TypeParamList [] =
    fail (unknown_loc, «Empty type parameters are not supported») ∧
  ptree_TypeParamList [t] =
    do
      expect_tok t RparT;
      return []
    od ∧
  ptree_TypeParamList (p::ps) =
    do
      expect_tok p CommaT;
      ptree_TypeParamList ps
    od ++
    do
      t <- ptree_TypeName p;
      ts <- ptree_TypeParamList ps;
      return (t::ts)
    od
End

Definition ptree_TypeParams_def:
  ptree_TypeParams (Lf (_, locs)) =
    fail (locs, «Expected a type-parameters non-terminal») ∧
  ptree_TypeParams (Nd (nterm, locs) args) =
    if nterm = INL nTypeParams then
      case args of
        [tv] =>
          fmap (λt. [t]) $ ptree_TypeName tv
      | lpar :: tv :: rest =>
          do
            expect_tok lpar LparT;
            tn <- ptree_TypeName tv;
            ts <- ptree_TypeParamList rest;
            return (tn::ts)
          od
      | _ => fail (locs, «Impossible: nTypeParams»)
    else
      fail (locs, «Expected a type-parameters non-terminal»)
End

Definition ptree_TypeDef_def:
  ptree_TypeDef (Lf (_, locs)) =
    fail (locs, «Expected a typedef non-terminal») ∧
  ptree_TypeDef (Nd (nterm, locs) args) =
    if nterm = INL nTypeDef then
      case args of
        [tps; id; info] =>
          do
            tys <- ptree_TypeParams tps;
            nm <- ptree_ConstrName id;
            trs <- ptree_TypeInfo info;
            return (locs, tys, nm, trs)
          od
      | [id; info] =>
          do
            nm <- ptree_ConstrName id;
            trs <- ptree_TypeInfo info;
            return (locs, [], nm, trs)
          od
      | _ => fail (locs, «Impossible: nTypeDef»)
    else
      fail (locs, «Expected a typedef non-terminal»)
End

Definition ptree_TypeDefs_def:
  ptree_TypeDefs (Lf (_, locs)) =
    fail (locs, «Expected a typedef:s non-terminal») ∧
  ptree_TypeDefs (Nd (nterm, locs) args) =
    if nterm = INL nTypeDefs then
      case args of
        [td] =>
          fmap (λt. [t]) $ ptree_TypeDef td
      | [td; andt; tds] =>
          do
            expect_tok andt AndT;
            t <- ptree_TypeDef td;
            ts <- ptree_TypeDefs tds;
            return (t::ts)
          od
      | _ => fail (locs, «Impossible: nTypeDefs»)
    else
      fail (locs, «Expected a typedef:s non-terminal»)
End

(* Ocaml datatype definitions and type abbreviations can be made mutually
 * recursive with each other and this is not supported in CakeML. Example:
 *   type foo = A of bar | B of baz | ...
 *   and baz = foo list
 *)

Definition ptree_TypeDefinition_def:
  ptree_TypeDefinition (Lf (_, locs)) =
    fail (locs, «Expected a type definition non-terminal») ∧
  ptree_TypeDefinition (Nd (nterm, locs) args) =
    if nterm = INL nTypeDefinition then
      case args of
        [typet; nrec; tds] =>
          do
            expect_tok typet TypeT;
            expect_tok nrec NonrecT;
            tdefs <- ptree_TypeDefs tds;
            if EVERY (λ(locs,tys,nm,trs). ISL trs) tdefs then
              return $ MAP (λ(locs,tys,nm,trs). Dtabbrev locs tys nm (OUTL trs))
                           tdefs
            else if EVERY (λ(locs,tys,nm,trs). ISR trs) tdefs then
              return $ [Dtype locs (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs))
                                        tdefs)]
            else
              fail (locs, concat [
                    «Type abbreviations and datatype definitions cannot be»;
                    « mutually recursive in CakeML»])
          od
      | [typet; tds] =>
          do
            expect_tok typet TypeT;
            tdefs <- ptree_TypeDefs tds;
            (abbrevs,datas) <<- PARTITION (λ(_,tys,nm,trs). ISL trs) tdefs;
            abbrevs <<-
              MAP (λ(locs,tys,nm,trs). Dtabbrev locs tys nm (OUTL trs))
                  abbrevs;
            datas <<-
              Dtype locs (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs)) datas);
            return (datas::abbrevs)
          od
      | _ => fail (locs, «Impossible: nTypeDefinition»)
    else
      fail (locs, «Expected a type definition non-terminal»)
End

(* Build a top-level letrec out of a list of let rec-bindings.
 *)

Definition build_dletrec_def:
  build_dletrec locs binds =
    Dletrec locs (MAP (λ(f,ps,x). (f,"",Mat (Var (Short ""))
                                    case ps of
                                      [] => [] (* this should never happen *)
                                    | p::ps =>
                                        [p, build_fun_lam x ps]))
                      binds)
End

(* Builds a top-level let out of a list of let bindings.
 *)

Definition build_dlet_def:
  build_dlet locs binds =
    MAP (λbind.
           case bind of
             INL (p, x) => Dlet locs p x
           | INR (f, ps, x) => Dlet locs (Pvar f) (build_fun_lam x ps))
        binds
End

Definition ptree_Definition_def:
  (ptree_Definition (Lf (_, locs)) =
    fail (locs, «Expected a top-level definition non-terminal»)) ∧
  (ptree_Definition (Nd (nterm, locs) args) =
    if nterm = INL nDefinition then
      case args of
        [arg] => ptree_Definition arg
      | _ => fail (locs, «Impossible: nDefinition»)
    else if nterm = INL nTopLet then
      case args of
        [lett; lbs] =>
          do
            expect_tok lett LetT;
            binds <- ptree_LetBindings lbs;
            return (build_dlet locs binds)
          od
      | _ => fail (locs, «Impossible: nTopLet»)
    else if nterm = INL nTopLetRec then
      case args of
        [lett; rect; lbs] =>
          do
            expect_tok lett LetT;
            expect_tok rect RecT;
            binds <- ptree_LetRecBindings lbs;
            return [build_dletrec locs binds]
          od
      | _ => fail (locs, «Impossible: nTopLetRec»)
    else if nterm = INL nTypeDefinition then
      ptree_TypeDefinition (Nd (nterm, locs) args)
    else if nterm = INL nExcDefinition then
      fmap (λd. [d]) $ ptree_ExcDefinition (Nd (nterm, locs) args)
    else if nterm = INL nOpen then
      fail (locs, «open-declarations are not supported (yet)»)
    else if nterm = INL nModuleDef then
      case args of
        [modt; modid; eq; mexpr] =>
          do
            expect_tok modt ModuleT;
            expect_tok eq EqualT;
            nm <- ptree_ModuleName modid;
            mx <- ptree_ModExpr mexpr;
            case mx of
              INL name =>
                fail (locs, «Structure assignment is not supported (yet?)»)
            | INR decs =>
                return [Dmod nm decs]
          od
      | _ => fail (locs, «Impossible: nModuleDef»)
    else
      fail (locs, «Expected a top-level definition non-terminal»)) ∧
  (ptree_ModExpr (Lf (_, locs)) =
    fail (locs, «Expected a module expression non-terminal»)) ∧
  (ptree_ModExpr (Nd (nterm, locs) args) =
    if nterm = INL nModExpr then
      case args of
        [path] => fmap INL $ ptree_ModulePath path
      | [struct; its; endt] =>
          do
            expect_tok struct StructT;
            expect_tok endt EndT;
            is <- ptree_ModuleItems its;
            return (INR is)
          od
      | _ => fail (locs, «Impossible: nModExpr»)
    else
      fail (locs, «Expected a module expression non-terminal»)) ∧
  (ptree_ModuleItems (Lf (_, locs)) =
    fail (locs, «Expected a module item list non-terminal»)) ∧
  (ptree_ModuleItems (Nd (nterm, locs) args) =
    if nterm = INL nModuleItems then
      ptree_Items args
    else
      fail (locs, «Expected a module item list non-terminal»)) ∧
  (ptree_Items [] =
    fail (unknown_loc, «Empty module item lists are not supported»)) ∧
  (ptree_Items [t] =
    fmap (λx. []) (expect_tok t SemisT) ++
    ptree_ModuleItem t) ∧
  (ptree_Items (t::ts) =
    do
      i <- ptree_ModuleItem t;
      is <- ptree_Items ts;
      return (i ++ is)
    od) ∧
  (ptree_ModuleItem (Lf (_, locs)) =
    fail (locs, «Expected a module item non-terminal»)) ∧
  (ptree_ModuleItem (Nd (nterm, locs) args) =
    if nterm = INL nModuleItem then
      case args of
        [semis; exdef] =>
          do
            expect_tok semis SemiT;
            x <- ptree_Expr nExpr exdef;
            return [Dlet locs (Pvar "") x]
          od ++
          ptree_Definition exdef
      | [exdef] =>
          do
            x <- ptree_Expr nExpr exdef;
            return [Dlet locs (Pvar "") x]
          od ++
          ptree_Definition exdef
      | _ => fail (locs, «Impossible: nModuleItem»)
    else
      fail (locs, «Expected a module item non-terminal»))
Termination
  WF_REL_TAC ‘measure (sum_size psize (sum_size psize (sum_size psize
                      (sum_size p1size psize))))’
End

Definition ptree_Start_def:
  ptree_Start (Lf (_, locs)) =
    fail (locs, «Expected the start non-terminal») ∧
  ptree_Start (Nd (nterm, locs) args) =
    if nterm = INL nStart then
      case args of
        [] => return []
      | [modits] => ptree_ModuleItems modits
      | _ => fail (locs, «Impossible: nStart»)
    else
      fail (locs, «Expected the start non-terminal»)
End

val _ = export_theory ();

